/**
 * This file is part of CamImportPlugins/SotonImportPlugins.
 * 
 * Copyright (C) 2011 intranda GmbH
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * @author Andrey Kozhushkov
 */
package de.intranda.goobi.plugins;

import java.io.BufferedInputStream;
import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.io.StringWriter;
import java.io.UnsupportedEncodingException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import net.xeoh.plugins.base.annotations.PluginImplementation;

import org.apache.commons.io.IOUtils;
import org.apache.commons.lang.StringUtils;
import org.apache.log4j.Logger;
import org.goobi.production.Import.Record;
import org.goobi.production.enums.ImportReturnValue;
import org.goobi.production.enums.ImportType;
import org.goobi.production.enums.PluginType;
import org.goobi.production.plugin.interfaces.IImportPlugin;
import org.goobi.production.plugin.interfaces.IPlugin;
import org.jdom.Namespace;
import org.jdom.Document;
import org.jdom.Element;
import org.jdom.JDOMException;
import org.jdom.input.SAXBuilder;
import org.jdom.output.Format;
import org.jdom.output.XMLOutputter;
import org.jdom.transform.XSLTransformer;

import ugh.dl.DigitalDocument;
import ugh.dl.DocStruct;
import ugh.dl.Fileformat;
import ugh.dl.Metadata;
import ugh.dl.MetadataType;
import ugh.dl.Prefs;
import ugh.exceptions.DocStructHasNoTypeException;
import ugh.exceptions.MetadataTypeNotAllowedException;
import ugh.exceptions.PreferencesException;
import ugh.exceptions.TypeNotAllowedForParentException;
import ugh.exceptions.WriteException;
import ugh.fileformats.mets.MetsMods;
import de.intranda.goobi.plugins.utils.ModsUtils;
import de.sub.goobi.Import.ImportOpac;
import de.sub.goobi.config.ConfigMain;

@PluginImplementation
public class CSICMixedImport implements IImportPlugin, IPlugin {

	/** Logger for this class. */
	private static final Logger logger = Logger.getLogger(CSICMixedImport.class);

	private static final String NAME = "CSICMixedImport";
	private static final String VERSION = "0.0.36000000";
//	private static final String XSLT_PATH = ConfigMain.getParameter("xsltFolder") + "MARC21slim2MODS3.xsl";
	private static final String XSLT_PATH = "resources/" + "MARC21slim2MODS3.xsl";
	private static final String MODS_MAPPING_FILE = "resources/" + "mods_map.xml";
//	private static final String MODS_MAPPING_FILE = ConfigMain.getParameter("xsltFolder") + "mods_map.xml";
	private static final String TEMP_DIRECTORY = ConfigMain.getParameter("tempfolder");

	// Namespaces
	private Namespace mets;
	private Namespace premis;
	private Namespace mix;
	private Namespace marc;
	private Namespace goobi;
	private Namespace mods;

	private Prefs prefs;
	private String data = "";
	private File importFile = null;
	private String importFolder = "output/";
	private Map<String, String> map = new HashMap<String, String>();
	private String currentIdentifier;
	private String currentTitle;
	private String currentAuthor;
	private List<String> currentCollectionList;
	private String encoding = "utf-8";

	/**
	 * Directory containing the image files (possibly in TIFF/JPEG subfolders)
	 */
//	public File exportFolder = new File("/opt/digiverso/goobi/0008_PCTN");

	 private File exportFolder = new File("samples/test");

	public CSICMixedImport() {
		map.put("?monographic", "Monograph");
		map.put("?continuing", "Periodical");
		map.put("?multipart monograph", "MultiVolumeWork");
		map.put("?single unit", "Monograph");
		map.put("?integrating resource", "MultiVolumeWork");
		map.put("?serial", "Periodical");
		map.put("?cartographic", "Map");
		map.put("?notated music", null);
		map.put("?sound recording-nonmusical", null);
		map.put("?sound recording-musical", null);
		map.put("?moving image", null);
		map.put("?three dimensional object", null);
		map.put("?software, multimedia", null);
		map.put("?mixed material", null);
	}

	/**
	 * not used
	 */
	@Override
	public Fileformat convertData() {
		return null;
	}
	
	/**
	 * replaces convertData() - returns a jDOM document rather than a Fileformat
	 * 
	 * @return
	 */
	public Document convertDocument() {
		if (data == null || data.isEmpty()) {
			logger.warn("Attempting to convert empty data. Aborting.");
			return null;
		}

		Document modsDoc = null;
		Document marcDoc = null;
		Document doc = null;
		File tempFile = new File(TEMP_DIRECTORY, "temp_" + System.currentTimeMillis() + ".xml");
		logger.debug("Creating temporary file " + tempFile.getAbsolutePath());
		try {
			doc = getDocumentFromString(data);
			getNamespaces(doc.getRootElement());
			marcDoc = getMarcDocument(doc);
			String marcString = getStringFromDocument(marcDoc, encoding);
			Fileformat ff = convertData(marcString);
			if (ff != null)
			{
				ff.write(tempFile.getAbsolutePath());
			}
			else {
				logger.error("Failed to convert marc doc");
				return null;
			}

			modsDoc = getDocumentFromFile(tempFile);
			getNamespaces(modsDoc.getRootElement());

		} catch (WriteException e) {
			logger.error(e.toString(), e);
		} catch (PreferencesException e) {
			logger.error(e.toString(), e);
		}

		doc = replaceXmlData(doc, modsDoc);
		doc = exchangeStructData(doc);
		doc = replaceStructData(doc, modsDoc);
		
		if(tempFile.exists())
			tempFile.delete();

		return doc;
	}

	/**
	 * 
	 * generate mets files and copy image files from record list
	 * 
	 */
	@Override
	public HashMap<String, ImportReturnValue> generateFiles(List<Record> records) {
		HashMap<String, ImportReturnValue> ret = new HashMap<String, ImportReturnValue>();

		int invalidImports = 0;
		int i = 0;
		for (Record record : records) {
			logger.info("parsing record " + ++i);
			data = record.getData();
			Document doc = convertDocument();
			logger.info("converted document " + getProcessTitle());
			if (doc != null) {
				try {
					File hotFile = new File(importFolder, getProcessTitle());
					logger.debug("Writing '" + hotFile.getAbsolutePath() + "' into hotfolder...");
					getFileFromDocument(hotFile, doc);
					logger.debug("copying image files...");
					copyImageFiles(exportFolder);
					ret.put(getProcessTitle(), ImportReturnValue.ExportFinished);
				} catch (IOException e) {
					logger.error(e.getMessage(), e);
					ret.put(getProcessTitle(), ImportReturnValue.WriteError);
				}
			} else {
				currentIdentifier = record.getId();
				ret.put(getProcessTitle(), ImportReturnValue.InvalidData);
				invalidImports++;
			}
		}
		if (invalidImports > 0)
			logger.warn(invalidImports + " of " + i + " imports did not succeed");
		return ret;
	}

	/**
	 * generate list of records
	 * 
	 */
	@Override
	public List<Record> generateRecordsFromFile() {
		List<Record> ret = new ArrayList<Record>();

		if (importFile.getName().endsWith("zip")) {
			logger.info("Extracting zip archive");
			ArrayList<String> recordStrings = unzipFile(importFile);

			int count = 0;
			for (String string : recordStrings) {
				logger.debug("Extracting record " + ++count);
				Record rec = new Record();
				rec.setData(string);
				ret.add(rec);
			}
		} else {
			logger.info("Importing single record file");
			InputStream input = null;
			StringWriter writer = null;
			try {
				logger.debug("loaded file: " + importFile.getAbsolutePath());
				input = new FileInputStream(importFile);
				Record record = new Record();
				writer = new StringWriter();
				IOUtils.copy(input, writer, encoding);
				record.setData(writer.toString());
				record.setId(importFile.getName().split("_")[0]);
				ret.add(record);

			} catch (FileNotFoundException e) {
				logger.error(e.getMessage(), e);
			} catch (IOException e) {
				logger.error(e.getMessage(), e);
			} finally {
				if (input != null) {
					try {
						if (writer != null)
							writer.close();
						input.close();
					} catch (IOException e) {
						logger.error(e.getMessage(), e);
					}
				}
				if (ret != null && importFile != null)
					logger.info("Extracted " + ret.size() + " records from '" + importFile.getName() + "'.");
				else
					logger.error("No record extracted from importFile");
			}
		}

		return ret;
	}

	/**
	 * not used - records are split on import
	 */
	@Override
	public List<Record> splitRecords(String records) {

		return null;
	}

	@Override
	public List<String> splitIds(String ids) {
		return null;
	}

	@Override
	public String getProcessTitle() {
		if (StringUtils.isNotBlank(currentTitle)) {
			return new ImportOpac().createAtstsl(currentTitle, currentAuthor).toLowerCase() + "_" + currentIdentifier + ".xml";
		}
		return currentIdentifier + ".xml";
	}

	@Override
	public void setData(Record r) {
		this.data = r.getData();
	}

	@Override
	public String getImportFolder() {
		return importFolder;
	}

	@Override
	public void setImportFolder(String folder) {
		this.importFolder = folder;
	}

	@Override
	public void setFile(File importFile) {
		this.importFile = importFile;
	}

	@Override
	public void setPrefs(Prefs prefs) {
		this.prefs = prefs;

	}

	@Override
	public List<ImportType> getImportTypes() {
		List<ImportType> answer = new ArrayList<ImportType>();
		answer.add(ImportType.FILE);

		return answer;
	}

	@Override
	public PluginType getType() {
		return PluginType.Import;
	}

	@Override
	public String getTitle() {
		return getDescription();
	}

	@Override
	public String getId() {
		return getDescription();
	}

	@Override
	public String getDescription() {
		return NAME + " v" + VERSION;
	}
	
	/**
	 * 
	 * Specialized convertData to convert only the specified String inString from marc to mods
	 * 
	 * @param inString
	 * @return
	 */
	private Fileformat convertData(String inString) {
		Fileformat ff = null;
		Document doc;
		try {
			doc = new SAXBuilder().build(new StringReader(inString));

			// remove namespaces
			Element docRoot = doc.getRootElement();
			docRoot = setNamespaceRecursive(docRoot, null);
			Element newRecord = new Element("record");
			List<Element> eleList = new ArrayList<Element>();
			for (Object obj : docRoot.getChildren()) {
				Element child = (Element) obj;
				eleList.add(child);
			}
			for (Element element : eleList) {
				element.detach();
			}
			newRecord.setContent(eleList);
			for (Object obj : newRecord.getChildren()) {
				Element child = (Element) obj;
				child.setNamespace(null);
			}
			newRecord = removeDuplicateChildren(newRecord);
			docRoot.detach();
			doc.setRootElement(newRecord);

			// logger.debug(new XMLOutputter().outputString(doc));
			if (doc != null && doc.hasRootElement()) {
				XSLTransformer transformer = new XSLTransformer(XSLT_PATH);
				Document docMods = transformer.transform(doc);
				
				// logger.debug(new XMLOutputter().outputString(docMods));
				ff = new MetsMods(prefs);
				DigitalDocument dd = new DigitalDocument();
				ff.setDigitalDocument(dd);

				Element eleMods = docMods.getRootElement();
				if (eleMods.getName().equals("modsCollection")) {
					eleMods = eleMods.getChild("mods", null);
				}

				// Determine the root docstruct type
				String dsType = "Monograph";
				if (eleMods.getChild("originInfo", null) != null) {
					Element eleIssuance = eleMods.getChild("originInfo", null).getChild("issuance", null);
					if (eleIssuance != null && map.get("?" + eleIssuance.getTextTrim()) != null) {
						dsType = map.get("?" + eleIssuance.getTextTrim());
					}
				}
				Element eleTypeOfResource = eleMods.getChild("typeOfResource", null);
				if (eleTypeOfResource != null && map.get("?" + eleTypeOfResource.getTextTrim()) != null) {
					dsType = map.get("?" + eleTypeOfResource.getTextTrim());
				}
				logger.debug("Docstruct type: " + dsType);

				DocStruct dsRoot = dd.createDocStruct(prefs.getDocStrctTypeByName(dsType));
				dd.setLogicalDocStruct(dsRoot);

				DocStruct dsBoundBook = dd.createDocStruct(prefs.getDocStrctTypeByName("BoundBook"));
				dd.setPhysicalDocStruct(dsBoundBook);
				// Collect MODS metadata
				ModsUtils.parseModsSection(MODS_MAPPING_FILE, prefs, dsRoot, dsBoundBook, eleMods);
				currentIdentifier = ModsUtils.getIdentifier(prefs, dsRoot);
				currentTitle = ModsUtils.getTitle(prefs, dsRoot);
				currentAuthor = ModsUtils.getAuthor(prefs, dsRoot);
				logger.debug("Author:" + currentAuthor + ", Title: " + currentTitle);
				
				//saving Mods file for debugging
				getFileFromDocument(new File("output/" + currentIdentifier + ".xml"), docMods);

				// Add 'pathimagefiles'
				try {
					Metadata mdForPath = new Metadata(prefs.getMetadataTypeByName("pathimagefiles"));
					mdForPath.setValue("./" + currentIdentifier);
					dsBoundBook.addMetadata(mdForPath);
				} catch (MetadataTypeNotAllowedException e1) {
					logger.error("MetadataTypeNotAllowedException while reading images", e1);
				} catch (DocStructHasNoTypeException e1) {
					logger.error("DocStructHasNoTypeException while reading images", e1);
				}

				// Add collection names attached to the current record
				if (currentCollectionList != null) {
					MetadataType mdTypeCollection = prefs.getMetadataTypeByName("singleDigCollection");
					for (String collection : currentCollectionList) {
						Metadata mdCollection = new Metadata(mdTypeCollection);
						mdCollection.setValue(collection);
						dsRoot.addMetadata(mdCollection);
					}
				}
			}
		} catch (JDOMException e) {
			logger.error(e.getMessage(), e);
			return null;
		} catch (IOException e) {
			logger.error(e.getMessage(), e);
		} catch (PreferencesException e) {
			logger.error(e.getMessage(), e);
		} catch (TypeNotAllowedForParentException e) {
			logger.error(e.getMessage(), e);
		} catch (MetadataTypeNotAllowedException e) {
			logger.error(e.getMessage(), e);
		}

		return ff;
	}

	private Element removeDuplicateChildren(Element newRecord) {
		Element newnewRecord = new Element(newRecord.getName());
		List<Element> children = newRecord.getChildren();
		List<String> tags = new ArrayList<String>();
		logger.debug("Cecking for duplicate datafields in " + children.size() + " fields");
		for (Element child : children) {
			if(child.getAttribute("tag")!=null && tags.contains(child.getAttributeValue("tag")))
			{
				logger.debug("Found duplicate MARC field with tag " + child.getAttributeValue("tag"));
			}
			else
			{
				logger.debug("Added tag " + child.getAttributeValue("tag") + " to tag list");
				newnewRecord.addContent((Element)child.clone());
				tags.add(child.getAttributeValue("tag"));
			}
		}
		
		return newnewRecord;
	}

	/**
	 * Extract marc section from import document and return it as its own document
	 * 
	 * @param inDoc
	 * @return
	 */
	private Document getMarcDocument(Document inDoc) {
		Element marcRecord = null;

		// getting document elements
		Element root = inDoc.getRootElement();

		logger.debug("getting document elements");
		if (root != null) {
			if (root.getChildren().isEmpty())
				logger.warn("No children found in root");
			else {
				marcRecord = root.getChild("dmdSec", mets).getChild("mdWrap", mets).getChild("xmlData", mets).getChild("marc", marc).getChild("record", marc);
			}
		} else
			logger.warn("Root element not found");
		marcRecord.detach();
		return new Document(marcRecord);
	}

	/**
	 * Get the namespaces using Element root
	 * 
	 * @param root
	 */
	private void getNamespaces(Element root) {
		mets = root.getNamespace("mets");
		if (mets != null)
			logger.debug("Namespace mets: Prefix = " + mets.getPrefix() + ", uri = " + mets.getURI());
		premis = root.getNamespace("premis");
		if (premis != null)
			logger.debug("Namespace premis: Prefix = " + premis.getPrefix() + ", uri = " + premis.getURI());
		mix = root.getNamespace("mix");
		if (mix != null)
			logger.debug("Namespace mix: Prefix = " + mix.getPrefix() + ", uri = " + mix.getURI());
		marc = root.getNamespace("marc");
		if (marc != null)
			logger.debug("Namespace marc: Prefix = " + marc.getPrefix() + ", uri = " + marc.getURI());
		goobi = root.getNamespace("goobi");
		if (goobi != null)
			logger.debug("Namespace goobi: Prefix = " + goobi.getPrefix() + ", uri = " + goobi.getURI());
		mods = root.getNamespace("mods");
		if (mods != null)
			logger.debug("Namespace mods: Prefix = " + mods.getPrefix() + ", uri = " + mods.getURI());
	}

	/**
	 * 
	 * Creates a single String out of the Document document
	 * 
	 * @param document
	 * @param encoding
	 * @return
	 */
	private String getStringFromDocument(Document document, String encoding) {
		if (document == null) {
			logger.warn("Trying to convert null document to String. Aborting");
			return null;
		}
		XMLOutputter outputter = new XMLOutputter();
		Format xmlFormat = outputter.getFormat();
		if (!(encoding == null) && !encoding.isEmpty())
			xmlFormat.setEncoding(encoding);
		xmlFormat.setExpandEmptyElements(true);
		outputter.setFormat(xmlFormat);
		String docString = outputter.outputString(document);

		return docString;
	}

	/**
	 * Load a jDOM document from an xml file
	 * 
	 * @param file
	 * @return
	 */
	private Document getDocumentFromFile(File file) {
		SAXBuilder builder = new SAXBuilder(false);
		Document document = null;

		try {
			document = builder.build(file);
		} catch (JDOMException e) {
			logger.error(e.toString(), e);
			return null;
		} catch (IOException e) {
			logger.error(e.toString(), e);
			return null;
		}
		return document;
	}

	/**
	 * Create a jDOM document from an xml string
	 * 
	 * @param string
	 * @return
	 */
	private Document getDocumentFromString(String string) {
		byte[] byteArray = null;
		try {
			byteArray = string.getBytes(encoding);
		} catch (UnsupportedEncodingException e1) {
		}
		ByteArrayInputStream baos = new ByteArrayInputStream(byteArray);

		// Reader reader = new StringReader(hOCRText);
		SAXBuilder builder = new SAXBuilder(false);
		Document document = null;

		try {
			document = builder.build(baos);
		} catch (JDOMException e) {
			System.err.println("error " + e.toString());
			return null;
		} catch (IOException e) {
			System.err.println(e.toString());
			return null;
		}
		return document;
	}

	/**
	 * Gets the "TYPE" of the logical structmap in Document doc
	 * 
	 * @param doc
	 * @return
	 */
	private String getLogicalType(Document doc) {
		List<Element> structMaps = doc.getRootElement().getChildren("structMap", mets);
		String type = null;
		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("LOGICAL")) {
				type = element.getChild("div", mets).getAttributeValue("TYPE");
				logger.debug("Found logical root type in marc document: " + type);
			}
		}
		return type;
	}

	/**
	 * Gets the "TYPE" of the physical structmap in Document doc
	 * 
	 * @param doc
	 * @return
	 */
	private String getPhysicalType(Document doc) {
		List<Element> structMaps = doc.getRootElement().getChildren("structMap", mets);
		String type = null;
		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("PHYSICAL")) {
				type = element.getChild("div", mets).getAttributeValue("TYPE");
				logger.debug("Found physical root type in marc document: " + type);
			}
		}
		return type;
	}



	/**
	 * Writes the Document doc into an xml File file
	 * 
	 * @param file
	 * @param doc
	 * @throws IOException
	 */
	private void getFileFromDocument(File file, Document doc) throws IOException {
		writeTextFile(getStringFromDocument(doc, encoding), file);
	}

	/**
	 * 
	 * Copy the files in exportFolder corresponding to the current record into the importFolder
	 * 
	 * @param exportFolder
	 */
	private void copyImageFiles(File exportFolder) {

		String id = currentIdentifier.replace("CSIC", "");

		if (!exportFolder.isDirectory()) {
			logger.warn("export folder does not exist. Cannot copy image files");
			return;
		}

		List<File> folders = Arrays.asList(exportFolder.listFiles());
		File tiffDir = null, jpegDir = null, imageDir = null;
		for (File file : folders) {
			if (file.isDirectory() && file.getName().contentEquals("Tiff")) {
				logger.debug("found \"tiff\" directory in " + exportFolder.getName());
				tiffDir = file;
			}
			if (file.isDirectory() && file.getName().contentEquals("JPG")) {
				logger.debug("found \"jpeg\" directory in " + exportFolder.getName());
				jpegDir = file;
			}
		}

		// with no tiff dir, we assume the process directories are directly
		// within exportFolder
		if (tiffDir == null) {
			for (File folder : folders) {
				if (folder.isDirectory() && folder.getName().contains(id))
					imageDir = folder;
				logger.debug("found export folder " + imageDir + " in " + exportFolder);
			}
		} else {
			// search in tiff-dir
			folders = Arrays.asList(tiffDir.listFiles());
			for (File folder : folders) {
				if (folder.isDirectory() && folder.getName().contains(id))
					imageDir = folder;
			}
			// if tiff-dir is empty or non-existant, search again in jpg dir
			if (imageDir == null || imageDir.listFiles() == null || imageDir.listFiles().length == 0) {
				folders = Arrays.asList(jpegDir.listFiles());
				for (File folder : folders) {
					if (folder.isDirectory() && folder.getName().contains(id))
						imageDir = folder;
					logger.debug("found export folder " + imageDir + " in " + jpegDir);
				}
			} else {
				logger.debug("found export folder " + imageDir + " in " + tiffDir);
			}
		}

		// check if we have an image Dir now
		if (imageDir == null || imageDir.listFiles() == null || imageDir.listFiles().length == 0) {
			logger.warn("No image dir found. Aborting image file import");
			return;
		}

		// get temp dir
		File tempDir = new File(importFolder, getProcessTitle().replace(".xml", ""));
		tempDir.mkdir();

		// parse all image Files and write them into new Files in the import
		// directory
		List<File> images = Arrays.asList(imageDir.listFiles(ImageFilter));
		for (File imageFile : images) {
			try {
				InputStream inStream = new FileInputStream(imageFile);
				BufferedInputStream bis = new BufferedInputStream(inStream);
				String filename = imageFile.getName();
				FileOutputStream fos = new FileOutputStream(new File(tempDir, filename));
				byte[] bytes = new byte[8192];
				int count = bis.read(bytes);
				while (count != -1 && count <= 8192) {
					fos.write(bytes, 0, count);
					count = bis.read(bytes);
				}
				if (count != -1) {
					fos.write(bytes, 0, count);
				}
				fos.close();
				bis.close();
			} catch (Exception e) {
				logger.error(e.getMessage(), e);
			}
		}
	}

	/**
	 * 
	 * makes the physical structMap of doc compatible with goobi
	 * 
	 * @param doc
	 * @param modsDoc
	 * @return
	 */
	private Document replaceStructData(Document doc, Document modsDoc) {

		Element physStruct = null, logStruct = null;
		List<Element> structMaps = doc.getRootElement().getChildren("structMap", mets);

		// set filegroup use to local
		Element fileSec = doc.getRootElement().getChild("fileSec", mets);
		if (fileSec != null) {
			Element fileGrp = fileSec.getChild("fileGrp", mets);
			fileGrp.setAttribute("USE", "LOCAL");
		}

		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("PHYSICAL"))
				physStruct = element;
			if (element.getAttributeValue("TYPE").contentEquals("LOGICAL"))
				logStruct = element;
		}

		// set type of logical root
		Element logRoot = null;
		for (Object obj : logStruct.getChildren("div", mets)) {
			if (obj instanceof Element)
				logRoot = (Element) obj;
			else
				break;

			logRoot.setAttribute("TYPE", getLogicalType(modsDoc));
		}

		// set type of physical root
		Element physRoot = null;
		for (Object obj : physStruct.getChildren("div", mets)) {
			if (obj instanceof Element)
				physRoot = (Element) obj;
			else
				break;

			physRoot.setAttribute("TYPE", getPhysicalType(modsDoc));
		}

		// remove "volume"
		List<Element> volumes = physRoot.getChildren();
		List<Element> volumeChildren = new ArrayList<Element>();
		int noVolumes = 0;
		for (Element volume : volumes) {
			if (volume.getAttributeValue("TYPE").contentEquals("VOLUME")) {
				volumeChildren.addAll(volume.cloneContent());
				noVolumes++;
			} else {
				volumeChildren.add(volume);
			}
		}
		if (noVolumes > 1)
			logger.warn("Number of volumes in book is " + noVolumes);
		physRoot.setContent(volumeChildren);

		// rename PAGE->page
		Iterator descendant = physRoot.getDescendants();
		while (descendant.hasNext()) {
			Element ele = null;
			Object obj = descendant.next();
			if (obj instanceof Element) {
				ele = (Element) obj;
				String value = ele.getAttributeValue("TYPE");
				if (value != null && value.contentEquals("PAGE"))
				{
					//Exchange values of LABEL and ORDERLABEL
//					String label = ele.getAttributeValue("LABEL");
//					String orderLabel = ele.getAttributeValue("ORDERLABEL");
//					ele.setAttribute("LABEL", orderLabel);
//					ele.setAttribute("ORDERLABEL", label);
					
					ele.setAttribute("TYPE", "page");
				}
			}

		}

		return doc;
	}

	/**
	 * Puts the logical StructData before physical StructData in the document structure of doc
	 * 
	 * @param doc
	 * @return
	 */
	private Document exchangeStructData(Document doc) {

		List<Element> structMaps = doc.getRootElement().getChildren("structMap", mets);
		Element structLink = doc.getRootElement().getChild("structLink", mets);
		Element physStruct = null, logStruct = null;
		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("PHYSICAL"))
				physStruct = element;
			if (element.getAttributeValue("TYPE").contentEquals("LOGICAL"))
				logStruct = element;
		}

		physStruct.detach();
		logStruct.detach();
		structLink.detach();

		doc.getRootElement().addContent(logStruct);
		doc.getRootElement().addContent(physStruct);
		doc.getRootElement().addContent(structLink);

		return doc;
	}

	/**
	 * 
	 * replaces the xmlData (actually the content of dmdSec) of doc with that of marcDoc
	 * 
	 * @param doc
	 * @param marcDoc
	 * @return
	 */
	private Document replaceXmlData(Document doc, Document marcDoc) {

		String dmdID = " ";

		// get old and new Dmd sections
		List<Element> newDmdSecs = marcDoc.getRootElement().getChildren("dmdSec", mets);

		// remove all Children of rootElement and save them as list
		List objects = doc.getRootElement().removeContent();
		List<Element> elements = new ArrayList<Element>();
		for (Object object : objects) {
			if (object instanceof Element) {
				elements.add((Element) object);
				logger.debug("adding Element to new root children list");
			}
		}

		// reattach all children of root, except "dmdSec", which is replaced by the two new sections
		for (Element element : elements) {
			if (element.getName().contentEquals("dmdSec")) {
				// get child of first dmdSec
				Element dmdChild = (Element) newDmdSecs.get(0).getChild("mdWrap", mets).clone();
				element.setContent(dmdChild);
				doc.getRootElement().addContent(element);

				if (newDmdSecs.size() > 1) // check if we have indeed two dmdSecs
				{
					Element newDmdSec2 = (Element) newDmdSecs.get(1).clone();
					dmdID = newDmdSec2.getAttributeValue("ID");
					doc.getRootElement().addContent(newDmdSec2);
				}
			} else {
				// all other elements, just reattach
				doc.getRootElement().addContent(element);
				// and set imagepath id for first child in physStructMap
				if (element.getName().contentEquals("structMap") && element.getAttributeValue("TYPE").contentEquals("PHYSICAL")) {
					logger.debug("adding reference DMDID=" + dmdID + " to physical structMap");
					Element book = element.getChild("div", mets);
					book.setAttribute("DMDID", dmdID);
				}
			}
		}
		return doc;
	}

	/**
	 * Unzip a zip archive and write results into Array of Strings
	 * 
	 * @param source
	 * @return
	 */
	private ArrayList<String> unzipFile(File source) {
		ArrayList<String> stringList = new ArrayList<String>();
		ArrayList<String> filenames = new ArrayList<String>();

		try {
			ZipInputStream in = new ZipInputStream(new BufferedInputStream(new FileInputStream(source)));
			ZipEntry entry;
			while ((entry = in.getNextEntry()) != null) {
				filenames.add(entry.getName());
				BufferedReader br = new BufferedReader(new InputStreamReader(in));  
				StringBuffer sb = new StringBuffer();  
				String line;  
				while ((line = br.readLine()) != null) {  
				  sb.append(line).append("\n");  
				}  
				stringList.add(sb.toString());
			}
		} catch (IOException e) {
			logger.error(e.toString(), e);
		}

		return stringList;
	}
	
	/**
	 * Sets the namespace of all Elements within Element root to Namespace ns
	 * 
	 * @param root
	 * @param ns
	 * @return
	 */
	public static Element setNamespaceRecursive(Element root, Namespace ns) {
		List<Element> current = new ArrayList<Element>();
		current.add(root);
		do {
			List<Element> children = new ArrayList<Element>();
			for (Element element : current) {
				element.setNamespace(ns);
				children.addAll(element.getChildren());
			}
			current = children;
		} while (!current.isEmpty());

		return root;
	}

	/**
	 * Read a text file and return content as String
	 * 
	 * @param file
	 * @return
	 */
	public static String readTextFile(File file) {
		String result = "";
		FileReader fileReader = null;
		BufferedReader reader = null;

		try {
			fileReader = new FileReader(file);
			reader = new BufferedReader(fileReader);

			String zeile = null;

			while ((zeile = reader.readLine()) != null) {
				// logger.debug("Reading line: " + zeile);
				result = result.concat(zeile + "\n");
			}
		} catch (FileNotFoundException e) {
			logger.error(e.toString(), e);
			return null;
		} catch (IOException e) {
			logger.error(e.toString(), e);
			return null;
		} finally {
			try {
				if (reader != null)
					reader.close();
			} catch (IOException e) {
				System.err.println("ERROR: " + e.toString());
			}
		}
		return result.trim();
	}
	
	/**
	 * Simply write a String into a text file
	 * 
	 * @param string
	 * @param file
	 * @return
	 * @throws IOException
	 */
	public static File writeTextFile(String string, File file) throws IOException {

		FileWriter writer = null;
		writer = new FileWriter(file);
		writer.write(string);
		if (writer != null)
			writer.close();

		return file;
	}

	public static void main(String[] args) throws PreferencesException, WriteException {
		CSICMixedImport converter = new CSICMixedImport();
		converter.prefs = new Prefs();
		
		try {
			converter.prefs.loadPrefs("resources/ruleset1.xml");
		} catch (PreferencesException e) {
			logger.error(e.getMessage(), e);
		}

		converter.setImportFolder("output/");
		List<Record> records = new ArrayList<Record>();
		if (!converter.exportFolder.isDirectory()) {
			logger.warn("No export directory found. Aborting");
			return;
		}

		for (File file : converter.exportFolder.listFiles(XmlFilter)) {

			converter.setFile(file);
			records.addAll(converter.generateRecordsFromFile());
		}

		HashMap<String, ImportReturnValue> results = converter.generateFiles(records);

		for (String key : results.keySet()) {
			System.out.println(key + " \t \t " + results.get(key));
		}
	}

	public static FilenameFilter ImageFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			// tif
			if (name.endsWith("tif") || name.endsWith("TIF")) {
				validImage = true;
			}

			// jpg
			if (name.endsWith("jpg") || name.endsWith("JPG") || name.endsWith("jpeg") || name.endsWith("JPEG")) {
				validImage = true;
			}

			return validImage;
		}
	};

	public static FilenameFilter XmlFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			if (name.endsWith("xml") || name.endsWith("XML")) {
				validImage = true;
			}

			return validImage;
		}
	};

	public static FilenameFilter zipFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			if (name.endsWith("zip") || name.endsWith("ZIP")) {
				validImage = true;
			}

			return validImage;
		}
	};
}
