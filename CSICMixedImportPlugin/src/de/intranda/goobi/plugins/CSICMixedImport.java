/**
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
import java.io.BufferedOutputStream;
import java.io.BufferedReader;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileFilter;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.io.StringWriter;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import net.xeoh.plugins.base.annotations.PluginImplementation;

import org.apache.commons.io.FileUtils;
import org.apache.commons.io.IOUtils;
import org.apache.commons.io.output.ByteArrayOutputStream;
import org.apache.commons.lang.StringUtils;
import org.apache.log4j.Logger;
import org.goobi.production.Import.DocstructElement;
import org.goobi.production.Import.ImportObject;
import org.goobi.production.Import.Record;
import org.goobi.production.enums.ImportReturnValue;
import org.goobi.production.enums.ImportType;
import org.goobi.production.enums.PluginType;
import org.goobi.production.plugin.interfaces.IImportPlugin;
import org.goobi.production.plugin.interfaces.IPlugin;
import org.goobi.production.properties.ImportProperty;
import org.jdom.Content;
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
import ugh.dl.DocStructType;
import ugh.dl.Fileformat;
import ugh.dl.Metadata;
import ugh.dl.MetadataType;
import ugh.dl.Prefs;
import ugh.exceptions.DocStructHasNoTypeException;
import ugh.exceptions.MetadataTypeNotAllowedException;
import ugh.exceptions.PreferencesException;
import ugh.exceptions.ReadException;
import ugh.exceptions.TypeNotAllowedAsChildException;
import ugh.exceptions.TypeNotAllowedForParentException;
import ugh.exceptions.WriteException;
import ugh.fileformats.mets.MetsMods;
import ugh.fileformats.mets.MetsModsImportExport;
import de.intranda.goobi.plugins.utils.ModsUtils;
import de.intranda.utils.CommonUtils;
import de.sub.goobi.Beans.Prozess;
import de.sub.goobi.Beans.Prozesseigenschaft;
import de.sub.goobi.Import.ImportOpac;
import de.sub.goobi.Persistence.ProzessDAO;
import de.sub.goobi.config.ConfigMain;
import de.sub.goobi.config.ConfigPlugins;
import de.sub.goobi.helper.Helper;
import de.sub.goobi.helper.exceptions.DAOException;
import de.sub.goobi.helper.exceptions.SwapException;

@PluginImplementation
public class CSICMixedImport implements IImportPlugin, IPlugin {

	/** Logger for this class. */
	private static final Logger logger = Logger.getLogger(CSICMixedImport.class);

	private static final String NAME = "CSICMixedImport";
	private static final String VERSION = "1.0.20120919.1";
	private static final String XSLT_PATH = ConfigMain.getParameter("xsltFolder") + "MARC21slim2MODS3.xsl";
	// private static final String XSLT_PATH = "resources/" + "MARC21slim2MODS3.xsl";
	// private static final String MODS_MAPPING_FILE = "resources/" + "mods_map.xml";
	private static final String MODS_MAPPING_FILE = ConfigMain.getParameter("xsltFolder") + "mods_map.xml";
	private static final String TEMP_DIRECTORY = ConfigMain.getParameter("tempfolder");

	private final static boolean deleteOriginalImages = true;
	private final static boolean deleteTempFiles = false;
	private final static boolean logConversionLoss = false;
	private final static boolean copyImages = true;
	private final static boolean copyPdfs = true;
	private final static boolean updateExistingRecords = true;

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
	private String importFolder = "/output";
	private Map<String, String> marcStructTypeMap = new HashMap<String, String>();
	private Map<String, String> anchorMap = new HashMap<String, String>();
	private Map<String, String> topStructMap = new HashMap<String, String>();
	private Map<String, String> logicalStructTypeMap = new HashMap<String, String>();
	private Map<String, VolumeInfo> recordMap = new HashMap<String, VolumeInfo>();
	private Map<String, String> projectsCollectionsMap = new HashMap<String, String>();
	private Map<String, Integer> pageVolumeMap = new HashMap<String, Integer>();
	private String currentIdentifier;
	private String currentTitle;
	private String currentAuthor;
	private String identifierSuffix;
	private List<String> currentCollectionList;
	private String encoding = "utf-8";
	private ArrayList<File> imageDirs = new ArrayList<File>();
	private ArrayList<File> pdfFiles = new ArrayList<File>();;
	public int currentVolume = 1;
	public int totalVolumes = 1;
	private String projectName;

	/**
	 * Directory containing the image files (possibly in TIFF/JPEG subfolders)
	 */
	// public File exportFolder = new File("/mnt/csic/");
	// public File exportFolder = new File("/opt/digiverso/ftp-import");
	public File exportFolder = new File(ConfigPlugins.getPluginConfig(this).getString("importFolder", "/opt/digiverso/ftp-import/"));
	public String projectIdentifierTitle = (ConfigPlugins.getPluginConfig(this).getString("projectIdentifier", "projectIdentifier"));
	public File sourceFolder = null;
	public File logFolder = new File("/opt/digiverso/logs/CSIC");

	// private File exportFolder = new File("example");

	public CSICMixedImport() {
		marcStructTypeMap.put("?monographic", "Monograph");
		// map.put("?continuing", "Periodical");
		marcStructTypeMap.put("?continuing", "PeriodicalVolume");
		// map.put("?multipart monograph", "MultiVolumeWork");
		marcStructTypeMap.put("?multipart monograph", "Volume");
		marcStructTypeMap.put("?single unit", "Monograph");
		// map.put("?integrating resource", "MultiVolumeWork");
		marcStructTypeMap.put("?integrating resource", "Volume");
		// map.put("?serial", "Periodical");
		marcStructTypeMap.put("?serial", "SerialVolume");
		marcStructTypeMap.put("?cartographic", "Map");
		marcStructTypeMap.put("?notated music", null);
		marcStructTypeMap.put("?sound recording-nonmusical", null);
		marcStructTypeMap.put("?sound recording-musical", null);
		marcStructTypeMap.put("?moving image", null);
		marcStructTypeMap.put("?three dimensional object", null);
		marcStructTypeMap.put("?software, multimedia", null);
		marcStructTypeMap.put("?mixed material", null);

		anchorMap.put("Monograph", "Series");
		anchorMap.put("Manuscript", "Series");
		anchorMap.put("SingleManuscript", "Series");
		anchorMap.put("SerialVolume", "Series");
		anchorMap.put("Volume", "MultiVolumeWork");
		anchorMap.put("PeriodicalVolume", "Periodical");

		logicalStructTypeMap.put("MANUSCRIPT", "Manuscript");
		logicalStructTypeMap.put("DOCUMENT", "MultiVolumeWork");
		logicalStructTypeMap.put("ITEM", "Volume");
		logicalStructTypeMap.put("MONOGRAPH", "Monograph");
		logicalStructTypeMap.put("JOURNAL", "Perodical");
		logicalStructTypeMap.put("VOLUME", "PeriodicalVolume");

		topStructMap.put("MultiVolumeWork", "Volume");
		topStructMap.put("Periodical", "PeriodicalVolume");
		topStructMap.put("Series", "SerialVolume");

		projectsCollectionsMap.put("0001_POQ", "BIBLIOTECAS#Museo Nacional de Ciencias Naturales (Biblioteca)");
		projectsCollectionsMap.put("0005_BETN", "BIBLIOTECAS#Centro de Ciencias Humanas y Sociales (Biblioteca Tomás Navarro Tomás)");
		projectsCollectionsMap.put("0006_PMSC", "BIBLIOTECAS#Centro de Ciencias Humanas y Sociales (Biblioteca Tomás Navarro Tomás)");
		projectsCollectionsMap.put("0006_PMSC_G_EEA", "BIBLIOTECAS#Centro de Estudios árabes GR-EEA");
		projectsCollectionsMap.put("0007_PCTN", "BIBLIOTECAS#Centro de Ciencias Humanas y Sociales (Biblioteca Tomás Navarro Tomás)");
		projectsCollectionsMap.put("0008_PCTN", "BIBLIOTECAS#Centro de Ciencias Humanas y Sociales (Biblioteca Tomás Navarro Tomás)");
		projectsCollectionsMap.put("0009_VCTN", "BIBLIOTECAS#Centro de Ciencias Humanas y Sociales (Biblioteca Tomás Navarro Tomás)");
		projectsCollectionsMap.put("0010_CMTN", "BIBLIOTECAS#Centro de Ciencias Humanas y Sociales (Biblioteca Tomás Navarro Tomás)");
		projectsCollectionsMap.put("0012_CIP", "BIBLIOTECAS#Museo Nacional de Ciencias Naturales (Biblioteca)");
		projectsCollectionsMap.put("0013_JAE", "BIBLIOTECAS#Museo Nacional de Ciencias Naturales (Biblioteca)");
		projectsCollectionsMap.put("0014_FMTN", "BIBLIOTECAS#Centro de Ciencias Humanas y Sociales (Biblioteca Tomás Navarro Tomás)");
		projectsCollectionsMap.put("0015_FAG", "BIBLIOTECAS#Centro de Estudios árabes GR-EEA");
		projectsCollectionsMap.put("0016_FAAD", "BIBLIOTECAS#Estación Experimental Aula Dei (Biblioteca) ");
		projectsCollectionsMap.put("0017_FACN", "BIBLIOTECAS#Museo Nacional de Ciencias Naturales (Biblioteca)");
		projectsCollectionsMap.put("0018_ACN_PC",
				"ARCHIVOS#Museo Nacional de Ciencias Naturales (Archivo)#Fondo Personal Científico#Ignacio Bolivar y Urrutia");
		projectsCollectionsMap.put("0030_CETN", "BIBLIOTECAS#Centro de Ciencias Humanas y Sociales (Biblioteca Tomás Navarro Tomás)");

	}

	private static DecimalFormat volumeNumberFormat = new DecimalFormat("00");

	private List<Record> generateRecords(Record r) {

		ArrayList<Record> records = new ArrayList<Record>();
		if (imageDirs == null || imageDirs.size() < 2) {
			// if we have no image directories or only one, create exactly one record
			records.add(r);
			if (imageDirs != null && !imageDirs.isEmpty()) {
				File pdfFile = null;
				if (pdfFiles != null && pdfFiles.size() > 0) {
					pdfFile = pdfFiles.get(0);
				}
				VolumeInfo info = new VolumeInfo(1, 1, imageDirs.get(0), pdfFile, identifierSuffix, projectName);
				recordMap.put(r.getId(), info);
				logger.debug("Adding record " + r.getId() + " to recordmap");
			}
		} else {
			int counter = 1;
			for (File imageDir : imageDirs) {

				String mySuffix = null;
				if (imageDir.getName().contains("_V")) {
					String volumeString = imageDir.getName().substring(imageDir.getName().lastIndexOf("_V"));
					mySuffix = volumeString.substring(1);
				}

				// create one new record for each image directory
				Record rec = new Record();
				if (mySuffix == null) {
					mySuffix = "V" + volumeNumberFormat.format(counter);
				}
				// get pdfDirectory
				File pdfFile = null;
				if (pdfFiles.size() == 1) {
					pdfFile = pdfFiles.get(0);
				} else if (pdfFiles.size() > 1) {
					for (File file : pdfFiles) {
						if (file.getName().toUpperCase().endsWith(mySuffix + ".PDF")) {
							pdfFile = file;
							break;
						}
					}
				}

				String suffix = (identifierSuffix == null ? mySuffix : identifierSuffix + "_" + mySuffix);
				rec.setId(r.getId() + "_" + mySuffix);
				rec.setData(r.getData());
				records.add(rec);
				VolumeInfo info = new VolumeInfo(counter, imageDirs.size(), imageDir, pdfFile, suffix, projectName);
				recordMap.put(rec.getId(), info);
				logger.debug("Adding record " + rec.getId() + " to recordmap");
				counter++;
			}
		}
		return records;
	}

	/**
	 * replaces convertData() - returns a jDOM document rather than a Fileformat
	 * 
	 * @return
	 */
	public Fileformat convertData() {
		if (data == null || data.isEmpty()) {
			logger.warn("Attempting to convert empty data. Aborting.");
			return null;
		}

		Document modsDoc = null;
		Document marcDoc = null;
		Document doc = null;
		File tempFile = new File(TEMP_DIRECTORY, "temp_" + System.currentTimeMillis() + ".xml");
		logger.debug("Creating temporary file " + tempFile.getAbsolutePath());
		Fileformat innerff = null;
		try {
			doc = CommonUtils.getDocumentFromString(data);

			// try {
			// CommonUtils.writeTextFile(data, new File(importFolder, "marc.txt"));
			// } catch (IOException e1) {
			// // TODO Auto-generated catch block
			// e1.printStackTrace();
			// }

			// System.out.println("Document from data-String:\n " + CommonUtils.getStringFromDocument(doc, encoding));
			getNamespaces(doc.getRootElement());
			marcDoc = getMarcDocument(doc);
			String marcString = getStringFromDocument(marcDoc, encoding);
			// System.out.println("String of MarcDocument:\n" + marcString);
			innerff = convertData(marcString);
			if (!deleteTempFiles && sourceFolder != null) {
				CommonUtils.writeTextFile(marcString, new File(sourceFolder, "marcDoc.xml"), encoding, false);
			}
			if (innerff != null) {
				innerff.write(tempFile.getAbsolutePath());
			} else {
				logger.error("Failed to convert marc doc");
				return null;
			}
			modsDoc = CommonUtils.getDocumentFromFile(tempFile);
			getNamespaces(modsDoc.getRootElement());

		} catch (WriteException e) {
			logger.error(e.toString(), e);
		} catch (PreferencesException e) {
			logger.error(e.toString(), e);
		} catch (JDOMException e) {
			logger.error(e.toString(), e);
		} catch (IOException e) {
			logger.error(e.toString(), e);
		}

		Element anchorElement = null;

		// verifyIdentifier();
		doc = replaceXmlData(doc, modsDoc);
		doc = exchangeStructData(doc);
		doc = replaceStructData(doc, anchorElement);

		// delete or move temporary files
		File anchorFile = new File(tempFile.getAbsolutePath().replace(".xml", "_anchor.xml"));
		try {
			if (deleteTempFiles && anchorFile.isFile()) {
				CommonUtils.moveFile(anchorFile, new File(importFolder, getProcessTitle().replace(".xml", "_anchor.xml")), true);
			} else if (anchorFile.isFile()) {
				copyFile(anchorFile, new File(importFolder, getProcessTitle().replace(".xml", "_anchor.xml")));
				if (sourceFolder != null && sourceFolder.isDirectory()) {
					CommonUtils.moveFile(anchorFile, new File(sourceFolder, anchorFile.getName()), true);
					// anchorFile.renameTo(new File(sourceFolder, anchorFile.getName()));
				}
			}
			if (deleteTempFiles && tempFile.exists()) {
				if (!tempFile.delete()) {
					logger.error("Unable to delete temp file");
				}
			} else if (tempFile.exists() && sourceFolder != null && sourceFolder.isDirectory()) {
				CommonUtils.moveFile(tempFile, new File(sourceFolder, tempFile.getName()), true);
				// tempFile.renameTo(new File(sourceFolder, tempFile.getName()));
			}
		} catch (IOException e) {
			logger.error(e.getMessage(), e);
		}

		// read document as fileformat
		Fileformat outerff = null;
		try {
			CommonUtils.getFileFromDocument(tempFile, doc);
			outerff = new MetsMods(prefs);
			outerff.read(tempFile.getAbsolutePath());
			compareFileFormats(innerff, outerff, anchorElement);
			removeOtherVolumes(outerff);
		} catch (PreferencesException e) {
			logger.error(e.toString());
		} catch (ReadException e) {
			logger.error(e.toString());
		} catch (IOException e) {
			logger.error(e.toString());
		}

		anchorFile = new File(tempFile.getAbsolutePath().replace(".xml", "_anchor.xml"));
		if (anchorFile.isFile()) {
			try {
				CommonUtils.moveFile(anchorFile, new File(importFolder, getProcessTitle().replace(".xml", "_anchor.xml")), true);
//			anchorFile.renameTo(new File(importFolder, getProcessTitle().replace(".xml", "_anchor.xml")));
			} catch (IOException e) {
				logger.error(e.toString());
			}
		}
		if (tempFile.exists()) {
			tempFile.delete();
		}

		return outerff;
	}

	private void removeOtherVolumes(Fileformat outerff) throws PreferencesException {

		// remove logical structures
		DocStruct topStruct = outerff.getDigitalDocument().getLogicalDocStruct();
		ArrayList<DocStruct> invalidDocStructs = new ArrayList<DocStruct>();
		if (topStruct.getType().isAnchor() && topStruct.getAllChildren().size() > 1) {
			for (int i = 1; i <= topStruct.getAllChildren().size(); i++) {
				if (i != currentVolume) {
					invalidDocStructs.add(topStruct.getAllChildren().get(i - 1));
					// topStruct.removeChild(topStruct.getAllChildren().get(i-1));
				}
			}
			for (DocStruct docStruct : invalidDocStructs) {
				topStruct.removeChild(docStruct);
			}

		}

		// remove physical structures
		DocStruct bookStruct = outerff.getDigitalDocument().getPhysicalDocStruct();
		ArrayList<DocStruct> invalidPages = new ArrayList<DocStruct>();
		for (DocStruct page : bookStruct.getAllChildren()) {
			String id = page.getIdentifier();
			// System.out.println("Checking page with id = " + id);
			Integer pageVolume = pageVolumeMap.get(id);
			if (pageVolume != null && pageVolume != currentVolume) {
				invalidPages.add(page);
				// bookStruct.removeChild(page);
			}
		}
		for (DocStruct docStruct : invalidPages) {
			bookStruct.removeChild(docStruct);
		}
	}

	private void compareFileFormats(Fileformat innerff, Fileformat outerff, Element anchorElement) {

		try {
			DocStruct innerLogStruct = innerff.getDigitalDocument().getLogicalDocStruct();
			DocStruct outerLogStruct = outerff.getDigitalDocument().getLogicalDocStruct();
			List<DocStruct> innerChildren = innerLogStruct.getAllChildren();
			List<DocStruct> outerChildren = outerLogStruct.getAllChildren();

			DocStructType innerAnchorType = null;
			DocStructType innerTopStructType = null;
			if (innerLogStruct.getType().isAnchor()) {
				innerAnchorType = innerLogStruct.getType();
				innerTopStructType = innerChildren.get(0).getType();
			} else {
				innerTopStructType = innerLogStruct.getType();
			}

			if (outerChildren != null && outerChildren.size() > 1 && outerChildren.size() == imageDirs.size()) {
				// each child ("item") corresponds to one volume

				// force DocTypes to MultiVolumeWork and Volume
				innerAnchorType = prefs.getDocStrctTypeByName("MultiVolumeWork");
				// innerTopStructType = prefs.getDocStrctTypeByName("Volume");

				int counter = 1;
				for (DocStruct docStruct : outerChildren) {
					// remove ds if not the current volume
					// if(counter != currentVolume) {
					// outerLogStruct.removeChild(docStruct);
					// }
					docStruct.setType(innerTopStructType);
					counter++;
				}
				// the outer anchor is not the inner anchor, which is only kept as metadata
				outerLogStruct.setType(innerAnchorType);
				outerLogStruct.setAllMetadata(outerLogStruct.getAllChildren().get(0).getAllMetadata());

			} else {
				// If we have children, they are probably divisions within one volume, so we leave them
				outerLogStruct.setType(innerTopStructType);
				if (innerAnchorType != null) {
					DocStruct anchor = innerLogStruct.copy(true, false);
					anchor.addChild(outerLogStruct.copy(true, true));
					outerff.getDigitalDocument().setLogicalDocStruct(anchor);
				}

			}

			// System.out.println("new level 1 docStruct = " + outerff.getDigitalDocument().getLogicalDocStruct().getType().getName());
			// System.out.println("new level 2 docStruct = " +
			// outerff.getDigitalDocument().getLogicalDocStruct().getAllChildren().get(0).getType().getName());

		} catch (PreferencesException e) {
			logger.error(e);
		} catch (TypeNotAllowedAsChildException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private boolean isChildTypeAllowed(DocStruct parent, DocStruct child) {
		List<String> allowedChildTypes = parent.getType().getAllAllowedDocStructTypes();

		if (allowedChildTypes == null || allowedChildTypes.isEmpty()) {
			return false;
		}

		for (String string : allowedChildTypes) {
			if (child.getType().getName().contentEquals(string)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * 
	 * generate mets files and copy image files from record list
	 * 
	 */
	@Override
	public List<ImportObject> generateFiles(List<Record> records) {
		ArrayList<ImportObject> ret = new ArrayList<ImportObject>();

		if (importFolder != null) {
			// sourceFolder =
		}

		// for (String id : recordMap.keySet()) {
		// System.out.println(id);
		// }

		for (Record r : records) {
			logger.info("Processing " + r.getId());
			// Data conversion
			data = r.getData();
			VolumeInfo info = recordMap.get(r.getId());
			// VolumeInfo info = (VolumeInfo)CommonUtils.getFromMap(recordMap, r.getId());
			if (info == null) {
				logger.error("Unable to find information to that record");
				continue;
			}
			currentVolume = info.volumeNumber;
			totalVolumes = info.totalVolumes;
			identifierSuffix = info.identifierSuffix;
			// currentCollectionList = r.getCollections();
			currentCollectionList = new ArrayList<String>();
			String collection = projectsCollectionsMap.get(info.projectName);
			if (collection != null) {
				currentCollectionList.add(collection);
			}
			Fileformat ff = convertData();

			ImportObject io = new ImportObject();

			if (ff != null) {

				// add collection as metadata
				addProject(ff, info.projectName);

				// writing converted data into Import("temp") folder
				try {
					MetsMods mm = new MetsMods(prefs);
					mm.setDigitalDocument(ff.getDigitalDocument());
					String fileName = getImportFolder() + getProcessTitle();
					logger.debug("Writing '" + fileName + "'...");
					mm.write(fileName);
					logger.debug("copying image files from " + info.imageDir.getAbsolutePath() + "...");
					copyImageFiles(info.imageDir);
					copyPdfs(info.pdfFile);
					io.setProcessTitle(getProcessTitle().replace(".xml", ""));
					io.setMetsFilename(fileName);
					io.setImportReturnValue(ImportReturnValue.ExportFinished);

					Prozesseigenschaft property = new Prozesseigenschaft();
					property.setTitel(projectIdentifierTitle);
					property.setWert(info.projectName);
					ArrayList<Prozesseigenschaft> propertyList = new ArrayList<Prozesseigenschaft>();
					propertyList.add(property);
					io.setProcessProperties(propertyList);

					if (importFile != null && sourceFolder != null) {
						try {
						CommonUtils.moveFile(importFile, new File(sourceFolder, importFile.getName()), true);
//						importFile.renameTo(new File(sourceFolder, importFile.getName()));
						} catch(IOException e) {
							logger.error(e.getMessage(), e);
						}
					}
				} catch (PreferencesException e) {
					logger.error(e.getMessage(), e);
					io.setImportReturnValue(ImportReturnValue.InvalidData);
					io.setErrorMessage(e.getMessage());
				} catch (WriteException e) {
					logger.error(e.getMessage(), e);
					io.setImportReturnValue(ImportReturnValue.WriteError);
					io.setErrorMessage(e.getMessage());
				}
			} else {
				io.setImportReturnValue(ImportReturnValue.InvalidData);
				io.setErrorMessage("FileFormat is null");
			}
			ret.add(io);
		}
		return ret;
	}

	private void addProject(Fileformat ff, String projectName) {
		try {
			DocStruct topStruct = ff.getDigitalDocument().getLogicalDocStruct();
			Metadata projectInfo = new Metadata(prefs.getMetadataTypeByName("ProjectIdentifier"));
			projectInfo.setValue(projectName);
			topStruct.addMetadata(projectInfo);

			// set also for first subSrtuct if topStruct was an anchor
			if (topStruct.getType().isAnchor()) {
				DocStruct subStruct = topStruct.getAllChildren().get(0);
				projectInfo = new Metadata(prefs.getMetadataTypeByName("ProjectIdentifier"));
				projectInfo.setValue(projectName);
				subStruct.addMetadata(projectInfo);
			}

		} catch (PreferencesException e) {
			logger.error("Unable to add collection as metadata: " + e.getMessage(), e);
		} catch (MetadataTypeNotAllowedException e) {
			logger.error("Unable to add collection as metadata: " + e.getMessage(), e);
		} catch (DocStructHasNoTypeException e) {
			logger.error("Unable to add collection as metadata: " + e.getMessage(), e);
		} finally {
		}

	}

	/**
	 * generate list of records
	 * 
	 */
	@Override
	public List<Record> generateRecordsFromFile() {
		List<Record> ret = new ArrayList<Record>();

		projectName = null;

		// String projectName = null;
		// projectName = importFile.getParentFile().getName();
		// if(projectName.toLowerCase().contains("mets")) {
		// projectName = importFile.getParentFile().getParentFile().getName();
		// }
		// logger.debug("Collection name is " + projectName);

		if (importFile.getName().endsWith("zip")) {
			logger.info("Extracting zip archive");
			HashMap<String, byte[]> recordStrings = unzipFile(importFile);
			HashMap<String, String> filteredRecordStrings = new HashMap<String, String>();

			// Check all records first to see what's inside
			int count = 0;
			for (String key : recordStrings.keySet()) {
				byte[] bytes = recordStrings.get(key);
				InputStream bais = null;
				if (key.endsWith(".zip")) {
					// Another zip-archive
					logger.debug("Extracting inner archive " + key + "; size = " + bytes.length + " bytes");
					try {
						bais = new ByteArrayInputStream(bytes);
						// FileOutputStream fout = new FileOutputStream(new File(importFolder, "temp.zip"));
						// fout.write(bytes);
						// fout.close();
						HashMap<String, String> tempRecords = unzipStream(bais);
						filteredRecordStrings.putAll(tempRecords);
					} catch (Exception e) {
						logger.error("Unable to read inner zip file");
					} finally {
						if (bais != null) {
							try {
								bais.close();
							} catch (IOException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
						}
					}
				} else if (key.endsWith(".xml")) {
					BufferedReader br = null;
					// ByteArrayInputStream bais = null;
					InputStreamReader isr = null;
					try {
						bais = new ByteArrayInputStream(bytes);
						isr = new InputStreamReader(bais);
						br = new BufferedReader(isr);
						StringBuffer sb = new StringBuffer();
						String line;
						while ((line = br.readLine()) != null) {
							sb.append(line).append("\n");
						}
						filteredRecordStrings.put(key, sb.toString());
					} catch (IOException e) {
						logger.error("Unable to read METS file from zip-Archive");
					} finally {
						try {
							if (bais != null) {
								bais.close();
							}
							if (isr != null) {
								isr.close();
							}
							if (br != null) {
								br.close();
							}
						} catch (IOException e) {
							logger.error("Error closing String reader");
						}
					}
				}
			}

			count = 0;
			for (String key : filteredRecordStrings.keySet()) {
				if (!key.endsWith(".xml")) {
					continue;
				}
				String importFileName = key;
				String importData = filteredRecordStrings.get(key);
				logger.debug("Extracting record " + ++count);
				Record rec = new Record();
				// System.out.println("Data from Zip-File:\n " + importData);
				rec.setData(importData);
				logger.debug("Getting record " + importFileName);
				rec.setId(importFileName.substring(0, importFileName.indexOf(".")));
				identifierSuffix = null;
				String searchString = parseImagefolder(rec); // get the image folders corresponding to this record, plus an additional process
				logger.debug("Project name is " + projectName);
				rec.setId(searchString); // identifer if necessary
				List<Record> records = generateRecords(rec);
				// check for old records
				for (Record record : records) {
					File oldFile = searchForExistingData(record.getId());
					if (oldFile != null) {
						if (updateExistingRecords) {
							logger.info("Found existing record. Updating.");
							if (!updateOldRecord(record, oldFile)) {
								Helper.setFehlerMeldung("Error updating record " + record.getId());
							} else {
								Helper.setMeldung("Updated process " + record.getId());
							}
						} else {
							Helper.setFehlerMeldung("Cannot import record " + record.getId() + " : A process with this title already exists.");
						}
					} else {
						ret.add(record);
					}
				}
			}
		} else {
			logger.info("Importing single record file");
			InputStream input = null;
			StringWriter writer = null;
			int updatedRecords = 0;
			try {
				logger.debug("loaded file: " + importFile.getAbsolutePath());
				String importFileName = importFile.getName();
				input = new FileInputStream(importFile);
				Record rec = new Record();
				writer = new StringWriter();
				IOUtils.copy(input, writer, encoding);
				rec.setData(writer.toString());
				rec.setId(importFileName.substring(0, importFileName.indexOf(".")));
				// check for old records
				identifierSuffix = null;
				String searchString = parseImagefolder(rec); // get the image folders corresponding to this record, plus an additional process
				rec.setId(searchString); // identifer if necessary
				List<Record> records = generateRecords(rec);
				// check for old records
				for (Record record : records) {
					File oldFile = searchForExistingData(record.getId());
					if (oldFile != null) {
						if (updateExistingRecords) {
							logger.info("Found existing record. Updating.");
							if (!updateOldRecord(record, oldFile)) {
								Helper.setFehlerMeldung("Error updating record " + record.getId());
							} else {
								Helper.setMeldung("Updated process " + record.getId());
								updatedRecords++;
							}
						} else {
							Helper.setFehlerMeldung("Cannot import record " + record.getId() + " : A process with this title already exists.");
						}
					} else {
						ret.add(record);
					}
				}
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
				if (ret.size() > 0 && importFile != null) {
					logger.info("Extracted " + ret.size() + " records from '" + importFile.getName() + "'.");
				} else if (updatedRecords > 0 && importFile != null) {
					logger.info("Updated " + updatedRecords + " records from '" + importFile.getName() + "'.");
				} else {
					logger.error("No record extracted from importFile");
				}
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
		String title = "";
		if (StringUtils.isNotBlank(currentTitle)) {
			String atstsl = new ImportOpac().createAtstsl(currentTitle, currentAuthor);
			if (atstsl != null) {
				title = new ImportOpac().createAtstsl(currentTitle, currentAuthor).toLowerCase() + "_" + currentIdentifier + ".xml";
			} else {
				title = currentIdentifier + ".xml";
			}
		} else {
			title = currentIdentifier + ".xml";
		}
		if (identifierSuffix != null && !identifierSuffix.isEmpty()) {
			return title.replace(".xml", "_" + identifierSuffix + ".xml");
		} else {
			return title;
		}
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
		answer.add(ImportType.FOLDER);

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
		StringReader sr = null;
		try {
			sr = new StringReader(inString);
			doc = new SAXBuilder().build(sr);

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
			// newRecord = removeDuplicateChildren(newRecord);
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
				String dsType = null;
				String dsAnchorType = null;

				// handle TypeOfResource
				List<Element> eleTypeOfResourceList = eleMods.getChildren("typeOfResource", null);
				if (eleTypeOfResourceList != null) {
					for (Element eleTypeOfResource : eleTypeOfResourceList) {
						if ("yes".equals(eleTypeOfResource.getAttributeValue("manuscript"))) {
							// Manuscript
							dsType = "SingleManuscript";
						} else if (marcStructTypeMap.get("?" + eleTypeOfResource.getTextTrim()) != null) {
							dsType = marcStructTypeMap.get("?" + eleTypeOfResource.getTextTrim());
						} else {
							dsType = "Monograph";
						}
					}
				}

				// handle issuance/frequency
				List<Element> eleOriginInfoList = eleMods.getChildren("originInfo", null);
				if (eleOriginInfoList != null) {
					for (Element eleOriginInfo : eleOriginInfoList) {
						Element eleIssuance = eleOriginInfo.getChild("issuance", null);
						if (eleIssuance != null && marcStructTypeMap.get("?" + eleIssuance.getTextTrim()) != null) {
							if (!dsType.contains("Manuscript") && marcStructTypeMap.get("?" + eleIssuance.getTextTrim()) != null) {
								dsType = marcStructTypeMap.get("?" + eleIssuance.getTextTrim());
							}
						}
						Element eleFrequency = eleOriginInfo.getChild("frequency", null);
						if (eleFrequency != null && eleFrequency.getValue() != null && !eleFrequency.getValue().isEmpty()) {
							// it has a frequency, therefore gets an anchor
							dsAnchorType = anchorMap.get(dsType);
							if (dsAnchorType == null) {
								dsAnchorType = "Series";
							}
						}
					}
				}

				// handle relatedSeries
				List<Element> eleRelatedSeriesList = eleMods.getChildren("relatedItem", null);
				if (eleRelatedSeriesList != null) {
					for (Element eleRelatedSeries : eleRelatedSeriesList) {

						if (eleRelatedSeries != null && eleRelatedSeries.getAttribute("type") != null
								&& eleRelatedSeries.getAttribute("type").getValue().contentEquals("series")) {
							if (dsAnchorType == null) {
								dsAnchorType = "Series";
							}
						}
					}
				}

				// if we still don't have an anchorType, but dsType requires one, create an appropriate one
				if (dsAnchorType == null) {
					if (dsType.contentEquals("PeriodicalVolume")) {
						dsAnchorType = "Periodical";
					} else if (dsType.contentEquals("Volume")) {
						dsAnchorType = "MultiVolumeWork";
					}
				} else { // There is an anchor
					if (dsType.contentEquals("SingleManuscript")) {
						dsType = "Manuscript";
					} else if (dsType.contentEquals("Monograph")) {
						dsType = "SerialVolume";
					}
				}

				logger.debug("Docstruct type: " + dsType);
				DocStruct dsVolume = dd.createDocStruct(prefs.getDocStrctTypeByName(dsType));
				if (dsVolume == null) {
					logger.error("Could not create DocStructType " + dsVolume);
					return null;
				}
				DocStruct dsAnchor = null;
				if (dsAnchorType != null) {
					dsAnchor = dd.createDocStruct(prefs.getDocStrctTypeByName(dsAnchorType));
					if (dsAnchor == null) {
						logger.error("Could not create DocStructType " + dsAnchorType);
					}
				}

				DocStruct dsBoundBook = dd.createDocStruct(prefs.getDocStrctTypeByName("BoundBook"));
				dd.setPhysicalDocStruct(dsBoundBook);
				// Collect MODS metadata
				ModsUtils.parseModsSection(MODS_MAPPING_FILE, prefs, dsVolume, dsBoundBook, dsAnchor, eleMods);
				currentIdentifier = ModsUtils.getIdentifier(prefs, dsVolume);
				currentTitle = ModsUtils.getTitle(prefs, dsVolume);
				currentAuthor = ModsUtils.getAuthor(prefs, dsVolume);
				logger.debug("Author:" + currentAuthor + ", Title: " + currentTitle);

				// create source ("import") Folder
				if (importFolder != null) {
					File tempDir = new File(importFolder, getProcessTitle().replace(".xml", ""));
					sourceFolder = new File(tempDir, "import");
					sourceFolder.mkdirs();
				}

				// Check if we are part of a series, and if so, create logical DocStruct accordingly
				try {
					List<? extends Metadata> seriesIDList = null;
					if (dsAnchor != null) {
						seriesIDList = dsAnchor.getAllMetadataByType(prefs.getMetadataTypeByName("CatalogIDDigital"));
					}
					// for (Metadata metadata : seriesIDList) {
					// }
					if (seriesIDList != null && !seriesIDList.isEmpty()) {
						logger.debug("Record is part of a series");
						// isSeriesVolume = true;
						dsAnchor.addChild(dsVolume);
						dd.setLogicalDocStruct(dsAnchor);
						String volumeName = dsVolume.getType().getName();
						if (volumeName.contentEquals("Monograph")) {
							dsVolume.setType(prefs.getDocStrctTypeByName("SerialVolume"));
						}
						if (volumeName.contentEquals("SingleManuscript")) {
							dsVolume.setType(prefs.getDocStrctTypeByName("Manuscript"));
						}
					} else {
						dd.setLogicalDocStruct(dsVolume);
						logger.debug("Record is not part of a series");
						String volumeName = dsVolume.getType().getName();
						if (volumeName.contentEquals("SerialVolume")) {
							dsVolume.setType(prefs.getDocStrctTypeByName("Monograph"));
						}
						if (volumeName.contentEquals("Manuscript")) {
							dsVolume.setType(prefs.getDocStrctTypeByName("SingleManuscript"));
						}
					}
				} catch (TypeNotAllowedAsChildException e) {
					logger.error("Child Type not allowed", e);
				}

				if (logConversionLoss) {
					try {
						File marcLossFile = new File(logFolder, currentIdentifier + "_MarcLoss.xml");
						Document lossDoc = getMarcModsLoss(doc, docMods);
						CommonUtils.getFileFromDocument(marcLossFile, lossDoc);
						File modsFile = new File(logFolder, currentIdentifier + "_Mods.xml");
						CommonUtils.getFileFromDocument(modsFile, docMods);
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}

				if (!deleteTempFiles) {
					try {
						File modsFile = new File(sourceFolder, "modsTemp.xml");
						CommonUtils.getFileFromDocument(modsFile, docMods);
					} catch (IOException e) {
						// TODO Auto-generated catch block
						e.printStackTrace();
					}
				}

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
						dsVolume.addMetadata(mdCollection);
						if (dsAnchor != null) {
							dsAnchor.addMetadata(mdCollection);
						}
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
		} finally {
			// try{
			if (sr != null) {
				sr.close();
			}
			// } catch(IOException e) {
			// logger.error("Error closing String reader");
			// }
		}

		return ff;
	}

	/**
	 * returns the metadatafile meta.xml if a prozess of this name was found, null otherwise
	 * 
	 * @param processTitle
	 * @return
	 */
	private File searchForExistingData(String processTitle) {
		String metsFilePath, processDataDirectory;
		ProzessDAO dao = new ProzessDAO();

		try {
			List<Prozess> processList = dao.search("from Prozess where titel LIKE '%" + processTitle + "'");

			if (processList != null && !processList.isEmpty()) {
				Prozess p = processList.get(0);
				logger.info("Found existing process '" + p.getTitel() + "'...");
				metsFilePath = p.getMetadataFilePath();
				processDataDirectory = p.getProcessDataDirectory();
				logger.debug("METS file path: " + metsFilePath);
				logger.debug("Process data path: " + processDataDirectory);
				File metadataFile = new File(metsFilePath);
				return metadataFile;
			}
		} catch (DAOException e) {
			logger.error(e.toString());
		} catch (SwapException e) {
			logger.error(e.toString());
		} catch (IOException e) {
			logger.error(e.toString());
		} catch (InterruptedException e) {
			logger.error(e.toString());
		}
		return null;
	}

	/**
	 * returns the metadatafile meta.xml if a prozess of this name was found, null otherwise
	 * 
	 * @param processTitle
	 * @return
	 */
	public static File DeleteExistingData(String processTitle) {
		String processDataDirectory = null;
		ProzessDAO dao = new ProzessDAO();

		try {
			List<Prozess> processList = dao.search("from Prozess where titel LIKE '%" + processTitle + "%'");

			logger.debug("Deleting " + processList.size() + "data sets.");
			if (processList != null && !processList.isEmpty()) {
				for (Prozess prozess : processList) {
					processDataDirectory = prozess.getProcessDataDirectory();
					dao.remove(prozess);
				}
				File prozessDir = new File(processDataDirectory);
				deleteOldDirs(prozessDir.getParentFile(), processTitle);
			}
		} catch (DAOException e) {
			logger.error(e.toString(), e);
		} catch (SwapException e) {
			logger.error(e.toString(), e);
		} catch (IOException e) {
			logger.error(e.toString(), e);
		} catch (InterruptedException e) {
			logger.error(e.toString(), e);
		}
		return null;
	}

	/**
	 * Deletes all goobi metadata directories contianing prozesses oft the given identifier
	 * 
	 * @param parentDir
	 * @param identifier
	 */
	private static void deleteOldDirs(File parentDir, String identifier) {
		File[] dirs = parentDir.listFiles(DirFilter);
		boolean delete = false;

		for (File dir : dirs) {
			File imageDir = new File(dir, "images");
			if (imageDir.isDirectory()) {
				File[] imageDirChildren = imageDir.listFiles(DirFilter);
				for (File childDir : imageDirChildren) {
					if (childDir.getName().contains(identifier))
						delete = true;
					break;
				}
			} else
				delete = true;
			if (delete) {
				logger.info("Deleting directory " + dir.getName());
				CommonUtils.deleteAllFiles(dir);
			}
		}

	}

	/**
	 * 
	 * creates a backup of the oldMetaFile and replaces the metafile with the Record record
	 * 
	 * @param record
	 * @param oldMetaFile
	 */
	private boolean updateOldRecord(Record record, File oldMetaFile) {

		VolumeInfo info = recordMap.get(record.getId());
		if (info == null) {
			logger.error("Unable to find information to that record");
			return false;
		}
		currentVolume = info.volumeNumber;
		totalVolumes = info.totalVolumes;
		identifierSuffix = info.identifierSuffix;

		data = record.getData();
		// currentCollectionList = r.getCollections();
		currentCollectionList = new ArrayList<String>();
		String collection = projectsCollectionsMap.get(info.projectName);
		if (collection != null) {
			currentCollectionList.add(collection);
		}
		Fileformat ff = convertData();
		logger.info("Replacing old matadata in metadata folder " + oldMetaFile.getParent() + " with new data");

		// renaming old metadata files to keep as backup
		String newMetaFileName = oldMetaFile.getAbsolutePath();
		File oldAnchorFile = new File(oldMetaFile.getParent(), "meta_anchor.xml");
		if (oldAnchorFile.isFile()) {
			oldAnchorFile.renameTo(new File(oldMetaFile.getParent(), oldAnchorFile.getName().replace(".xml", ".preIntrandaImport.xml")));
		}
		oldMetaFile.renameTo(new File(oldMetaFile.getParent(), oldMetaFile.getName().replace(".xml", ".preIntrandaImport.xml")));
		try {
			if (ff == null) {
				logger.error("Mets document is null. Aborting import");
			}
			String fileName = newMetaFileName;
			logger.debug("Writing '" + fileName + "' into existing folder...");
			ff.write(fileName);
			copyImageFiles(info.imageDir);
			copyPdfs(info.pdfFile);
			// getting anchor file
			File importDir = new File(importFolder);
			if (!importDir.isDirectory()) {
				logger.warn("no hotfolder found. Cannot get anchor files");
			} else {

				File tempFolder = new File(importFolder, getProcessTitle().replace(".xml", ""));
				if (tempFolder.isDirectory()) {
					CommonUtils.moveDir(tempFolder, oldMetaFile.getParentFile(), true);
					// for (File dir : tempFolder.listFiles(DirFilter)) {
					// org.apache.commons.io.FileUtils.moveDirectory(dir, new File(oldMetaFile.getParentFile(), dir.getName()));
					// }
					// FileUtils.deleteDirectory(tempFolder);
				}

				// purging old temp files
				for (File file : importDir.listFiles(XmlFilter)) {
					if (file.getName().contains(record.getId()))
						file.delete();
				}

			}

			// ret.put(getProcessTitle(), ImportReturnValue.ExportFinished);
		} catch (IOException e) {
			logger.error(e.getMessage(), e);
			return false;
		} catch (WriteException e) {
			logger.error(e.getMessage(), e);
			return false;
		} catch (PreferencesException e) {
			logger.error(e.getMessage(), e);
			return false;
		}
		return true;
	}

	/**
	 * Removes all duplicate occurences of marc datafields with the same same tag
	 * 
	 * @param newRecord
	 * @return
	 */
	@SuppressWarnings({ "unchecked", "unused" })
	private Element removeDuplicateChildren(Element newRecord) {
		Element newnewRecord = new Element(newRecord.getName());
		List<Element> children = newRecord.getChildren();
		List<String> tags = new ArrayList<String>();
		logger.debug("Cecking for duplicate datafields in " + children.size() + " fields");
		for (Element child : children) {
			if (child.getAttribute("tag") != null && tags.contains(child.getAttributeValue("tag"))) {
				logger.debug("Found duplicate MARC field with tag " + child.getAttributeValue("tag"));
			} else {
				logger.debug("Added tag " + child.getAttributeValue("tag") + " to tag list");
				newnewRecord.addContent((Element) child.clone());
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
				marcRecord = root.getChild("dmdSec", mets).getChild("mdWrap", mets).getChild("xmlData", mets).getChild("marc", marc)
						.getChild("record", marc);
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
	 * Gets the "TYPE" of the logical structmap in Document doc
	 * 
	 * @param doc
	 * @return
	 */
	@SuppressWarnings("unchecked")
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
	 * Gets the "TYPE" of the logical structmap in Document doc
	 * 
	 * @param doc
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private String getLogicalSubType(Document doc) {
		List<Element> structMaps = doc.getRootElement().getChildren("structMap", mets);
		String type = null;
		for (Element element : structMaps) {
			if (element.getAttributeValue("TYPE").contentEquals("LOGICAL")) {

				Element series = element.getChild("div", mets);

				type = series.getChild("div", mets).getAttributeValue("TYPE");
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
	@SuppressWarnings("unchecked")
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
	 * Gets the corrsponding image folders and if necessary constructs a suffix to the identifier to distinguish this record from others with the same
	 * identifier. Returns a unique identifier String for this record
	 * 
	 * 
	 * @param r
	 * @return
	 */
	private String parseImagefolder(Record r) {

		imageDirs = new ArrayList<File>();
		pdfFiles = new ArrayList<File>();

		// identifiers of metadata file
		String id = r.getId();
		String identifier = null;
		String pieceDesignation = null;
		String volumeIdentifier = null;
		int volumeNumber = 0;
		String[] idParts = id.split("_");
		if (idParts == null || idParts.length == 0) {
			return null;
		}
		if (idParts[0].contentEquals("M") && idParts.length > 1) {
			identifier = idParts[1];
		} else {
			identifier = idParts[0];
		}
		if (idParts.length > 1) {
			int last = idParts.length - 1;
			if (idParts[last].startsWith("V") && idParts[last].length() < 5) {
				volumeIdentifier = idParts[last];
				try {
					volumeNumber = Integer.valueOf(volumeIdentifier.replaceAll("\\D", ""));
				} catch (NumberFormatException e) {
					logger.error("Found volume idenfier " + volumeIdentifier + " but could not extract volume number from it.");
				}
				pieceDesignation = idParts[last - 1];
			} else {
				pieceDesignation = idParts[last];
			}
			if (pieceDesignation != null && pieceDesignation.contentEquals(identifier)) {
				// what we thought was the pieceDesignation was actually the identifier field
				pieceDesignation = null;
			}
		}
		// if(identifier != null) {
		// currentIdentifier = identifier;
		// }

		// getting matching image folders
		if (!exportFolder.isDirectory()) {
			logger.warn("export folder does not exist. Cannot copy image files");
			return identifier;
		}

		File[] projectFolders = exportFolder.listFiles();
		for (File folder : projectFolders) {
			if (!folder.isDirectory() || !folder.getName().startsWith("00")) {
				continue;
			}

			projectName = folder.getName();
			identifierSuffix = null;
			logger.debug("Found project " + projectName);

			// if(projectName != null) {
			// for (File dir : exportFolder.listFiles()) {
			// if(dir.isDirectory() && dir.getName().contentEquals(projectName)) {
			// exportFolder = dir;
			// break;
			// }
			// }
			// }

			List<File> folders = Arrays.asList(folder.listFiles());
			File tiffDir = null, jpegDir = null, pdfDir = null, parentImageDir = null;
			for (File file : folders) {
				if (file.isDirectory() && file.getName().toLowerCase().contentEquals("tiff")) {
					logger.debug("found \"tiff\" directory in " + folder.getName());
					tiffDir = file;
				}
				if (file.isDirectory()
						&& (file.getName().toLowerCase().contentEquals("jpg") || file.getName().toLowerCase().contentEquals("difusion"))) {
					logger.debug("found \"jpeg\" directory in " + folder.getName());
					jpegDir = file;
				}
				if (file.isDirectory() && file.getName().toLowerCase().contentEquals("pdf")) {
					logger.debug("found \"pdf\" directory in " + folder.getName());
					pdfDir = file;
				}
			}

			// // set the appropriate parent directory containing the image archives
			// if (tiffDir == null || !tiffDir.isDirectory()) {
			// // if (jpegDir == null || !jpegDir.isDirectory()) {
			// parentImageDir = exportFolder;
			// // } else {
			// // parentImageDir = jpegDir;
			// // }
			// } else {
			// parentImageDir = tiffDir;
			// }

			List<File> processFolders = Arrays.asList(folder.listFiles());
			List<File> tiffFolders = null;
			if (tiffDir != null) {
				tiffFolders = Arrays.asList(tiffDir.listFiles());
			}
			ArrayList<File> idImageDirs = new ArrayList<File>();
			// Get image dirs matching the identifier
			for (File file : processFolders) {
				if (file.isDirectory() && file.getName().contains(identifier)) {
					idImageDirs.add(file);
					logger.debug("found export folder " + file.getName() + " in " + folder.getAbsolutePath());
				}
			}
			if (tiffFolders != null) {
				for (File file : tiffFolders) {
					if (file.isDirectory() && file.getName().contains(identifier)) {
						idImageDirs.add(file);
						logger.debug("found export folder " + file.getName() + " in " + tiffDir.getAbsolutePath());
					}
				}
			}

			if (idImageDirs == null || idImageDirs.isEmpty()) {
				continue;
			}

			// from these, get image dirs actually matching the metadata-file
			if (idImageDirs.size() == 1) {
				imageDirs.add(idImageDirs.get(0));
			} else {
				for (File dir : idImageDirs) {
					if (pieceDesignation == null || dir.getName().contains("_" + pieceDesignation)) {
						if (volumeIdentifier == null || dir.getName().contains("_" + volumeIdentifier)) {
							imageDirs.add(dir);
						}
					}
				}
			}

			// sort imageDirs by name
			if (imageDirs != null && !imageDirs.isEmpty()) {
				Collections.sort(imageDirs);
			}

			if (idImageDirs.size() > imageDirs.size()) {
				// there is at least one other process with the same identifier. Add volume or pieceDesignation to this identifier
				if (volumeIdentifier != null) {
					identifierSuffix = volumeIdentifier;
				} else {
					identifierSuffix = pieceDesignation;
				}
			}

			String logString = "Found the following image directories:";
			if (imageDirs != null && !imageDirs.isEmpty()) {
				for (File file : imageDirs) {
					logString += ("\n" + file.getAbsolutePath());
				}
			} else {
				logString += "\nNONE";
			}
			logger.debug(logString);

			// get pdfFile if one exists
			if (pdfDir != null) {
				for (File file : pdfDir.listFiles(pdfFilter)) {
					if (file.getName().contains(identifier)) {
						// pdf has the correct identifier, check if is matches the volume as well
						if (idImageDirs.size() < 2 || imageDirs.size() == idImageDirs.size()
								|| (volumeIdentifier != null && file.getName().contains(volumeIdentifier))
								|| (pieceDesignation != null && file.getName().contains(pieceDesignation))) {
							pdfFiles.add(file);
							logger.debug("Found pdf-file " + file.getAbsolutePath());
						}
					}
				}
			}

			if (identifierSuffix != null) {
				return identifier + "_" + identifierSuffix;
			} else {
				return identifier;
			}
		}
		return null;
	}

	/**
	 * 
	 * Copy the files in exportFolder corresponding to the current record into the importFolder
	 * 
	 * @param exportFolder
	 */
	private void copyImageFiles(File imageDir) {

		if (!copyImages || imageDir == null || imageDir.listFiles(ImageFilter) == null || imageDir.listFiles(ImageFilter).length == 0) {
			logger.debug("No images to copy");
			return;
		}

		// get temp dir
		File tempDir = new File(importFolder, getProcessTitle().replace(".xml", ""));
		File tempImageDir = new File(tempDir, "images");
		File tempTiffDir = new File(tempImageDir, getProcessTitle().replace(".xml", "") + "_tif");
		File tempOrigDir = new File(tempImageDir, "orig_" + getProcessTitle().replace(".xml", "") + "_tif");
		tempTiffDir.mkdirs();

		// parse all image Files and write them into new Files in the import
		// directory
		List<File> images = Arrays.asList(imageDir.listFiles(ImageFilter));
		for (File imageFile : images) {
			try {
				String filename = imageFile.getName();
				if (!deleteOriginalImages) {
					copyFile(imageFile, new File(tempTiffDir, filename));
					logger.debug("Copying image " + filename);
				} else {
					CommonUtils.moveFile(imageFile, new File(tempTiffDir, filename), true);
//					if (!imageFile.renameTo(new File(tempTiffDir, filename))) {
//						copyFile(imageFile, new File(tempTiffDir, filename));
//						imageFile.delete();
//					}
				}
				// if (deleteOriginalImages) {
				// imageFile.delete();
				// }
			} catch (Exception e) {
				logger.error(e.getMessage(), e);
			}
		}
	}

	private void copyFile(File source, File dest) throws IOException {
		InputStream inStream = new FileInputStream(source);
		BufferedInputStream bis = new BufferedInputStream(inStream);
		FileOutputStream fos = new FileOutputStream(dest);
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
	}

	private void copyPdfs(File pdfFile) {

		if (!copyPdfs || pdfFile == null) {
			logger.debug("No pdf to copy");
			return;
		}

		// get temp dir
		File tempDir = new File(importFolder, getProcessTitle().replace(".xml", ""));
		File tempOcrDir = new File(tempDir, "ocr");
		File tempPdfDir = new File(tempOcrDir, getProcessTitle().replace(".xml", "") + "_pdf");
		tempPdfDir.mkdirs();

		try {
			splitPdf(pdfFile, tempPdfDir);
			if (deleteOriginalImages) {
				pdfFile.delete();
			}
		} catch (Exception e) {
			logger.error(e.getMessage(), e);
		}
	}

	/**
	 * 
	 * makes the physical and logical structMap of doc compatible with goobi
	 * 
	 * @param doc
	 * @param anchorElement
	 *            the document's anchor as jDom Element. must be inserted into the ff afterwards
	 * @return
	 */
	@SuppressWarnings("unchecked")
	private Document replaceStructData(Document doc, Element anchorElement) {

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

		// make physDocStrct comply to BoundBook->page
		// set type of physical root
		Element physRoot = null;
		for (Object obj : physStruct.getChildren("div", mets)) {
			if (obj instanceof Element) {
				physRoot = (Element) obj;
				break;
			} else {
				continue;
			}
		}
		physRoot.setAttribute("TYPE", "BoundBook");
		List<Element> volumes = physRoot.getChildren();
		List<Element> pages = new ArrayList<Element>();
		int noVolumes = 0;

		// get all pages in the physical DocStruct
		for (Element volume : volumes) {
			noVolumes++;
			pages.addAll(getPhysicalPages(volume));
		}

		// remove all children of the physical root (BoundBook)
		physRoot.removeChildren("div", mets);

		// add all pages to the physical root (BoundBook)
		for (Element element : pages) {
			physRoot.addContent((Element) element.clone());
		}

		// rename PAGE->page
		Iterator<Content> descendant = physRoot.getDescendants();
		while (descendant.hasNext()) {
			Element ele = null;
			Object obj = descendant.next();
			if (obj instanceof Element) {
				ele = (Element) obj;
				String value = ele.getAttributeValue("TYPE");
				if (value != null && value.contentEquals("PAGE")) {
					// Exchange values of LABEL and ORDERLABEL
					String label = ele.getAttributeValue("LABEL");
					String orderLabel = ele.getAttributeValue("ORDERLABEL");
					ele.setAttribute("LABEL", orderLabel);
					ele.setAttribute("ORDERLABEL", label);

					ele.setAttribute("TYPE", "page");
				}
			}
		}

		// // verify logical names
		// verifyStructureNames(logStruct);
		//
		// // remove the anchor to be able to read the file as ff
		// List<? extends Content> logChildren = logStruct.getChildren();
		// if (logChildren != null && logChildren.size() > 0) {
		// if (logChildren.size() == 1) {
		// Content topContent = logChildren.get(0);
		// if (topContent instanceof Element) {
		// Element topElement = (Element) topContent;
		// String type = topElement.getAttributeValue("TYPE");
		// if (anchorMap.containsValue(type)) {
		// logger.debug("Logical DocStruct contains an anchor");
		//
		// List<? extends Content> list = logStruct.getContent();
		// for (int i = 0; i < list.size(); i++) {
		// Content content = list.get(i);
		// if (content instanceof Element) {
		// anchorElement = (Element) logStruct.removeContent(i);
		// break;
		// }
		// }
		// if (anchorElement != null) {
		// List<? extends Content> contentList = anchorElement.removeContent();
		// logStruct.addContent(contentList);
		// // int counter = 1;
		// // for (Content content : contentList) {
		// // if(content instanceof Element) {
		// // if(counter == currentVolume) {
		// // logStruct.addContent(content);
		// // }
		// // counter++;
		// // } else {
		// // logStruct.addContent(content);
		// // }
		// // }
		// if (imageDirs.size() < 2) {
		// // only one volume, so ignore the anchor
		// anchorElement = null;
		// }
		// } else {
		// logger.error("Found no anchor element!");
		// }
		// } else {
		// logger.debug("No anchor in logical DocStruct");
		// }
		// }
		// } else {
		// logger.error("Logical DocStruct has more than one child element");
		// }
		// } else {
		// logger.error("Logical DocStruct does not appear to have any child elements");
		// }

		return doc;
	}

	private void verifyStructureNames(Element structure) {
		List<Element> children = structure.getChildren("div", mets);
		if (children == null || children.isEmpty()) {
			return;
		}

		String parentType = null;
		if (structure.getName().contentEquals("div")) {
			parentType = structure.getAttributeValue("TYPE");
		}

		for (Element element : children) {
			String type = element.getAttributeValue("TYPE");
			if (type != null) {
				String tempType = logicalStructTypeMap.get(type);
				if (tempType != null) {
					type = tempType;
				}
				if (anchorMap.get(type) != null && parentType != null && !anchorMap.get(type).contentEquals(parentType)) {
					// if this element can have an anchor, and an anchor element exists, but cannot be an anchor of this element, change the element
					// type
					tempType = topStructMap.get(parentType);
					logger.debug("Setting DocStrct type to " + tempType + " to conform with anchor type " + parentType);
					if (tempType != null) {
						type = tempType;
					}
				}
				element.setAttribute("TYPE", type);
			}
			verifyStructureNames(element);
		}
	}

	private ArrayList<Element> getPhysicalPages(Element parent) {

		ArrayList<Element> pages = new ArrayList<Element>();

		List children = parent.getChildren();
		int volume = 0;
		try {
			volume = Integer.valueOf(parent.getAttributeValue("ORDER"));
		} catch (Exception e) {

		}
		for (Object object : children) {
			if (object instanceof Element) {
				Element child = (Element) object;
				if (child.getAttributeValue("TYPE").toLowerCase().contentEquals("page")) {
					// child is a page
					pages.add(child);
					if (volume != 0) {
						// map the volume this page belongs to
						pageVolumeMap.put(child.getAttributeValue("ID"), volume);
					}

				} else {
					pages.addAll(getPhysicalPages(child));
				}
			}
		}

		return pages;
	}

	/**
	 * Puts the logical StructData before physical StructData in the document structure of doc
	 * 
	 * @param doc
	 * @return
	 */
	@SuppressWarnings("unchecked")
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
	@SuppressWarnings("unchecked")
	private Document replaceXmlData(Document doc, Document marcDoc) {

		String dmdID = " ";

		// get old and new Dmd sections
		List<Element> newDmdSecs = marcDoc.getRootElement().getChildren("dmdSec", mets);

		// remove all Children of rootElement and save them as list
		List<Content> objects = doc.getRootElement().removeContent();
		List<Element> elements = new ArrayList<Element>();
		for (Content content : objects) {
			if (content instanceof Element) {
				elements.add((Element) content);
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
	private HashMap<String, byte[]> unzipFile(File source) {
		ArrayList<String> stringList = new ArrayList<String>();
		ArrayList<String> filenames = new ArrayList<String>();
		HashMap<String, byte[]> contentMap = new HashMap<String, byte[]>();

		FileInputStream fis = null;
		BufferedInputStream bis = null;
		ZipInputStream in = null;
		try {
			fis = new FileInputStream(source);
			bis = new BufferedInputStream(fis);
			in = new ZipInputStream(bis);
			ZipEntry entry;
			while ((entry = in.getNextEntry()) != null) {
				filenames.add(entry.getName());
				logger.debug("Unzipping file " + entry.getName() + " from archive " + source.getName());
				ByteArrayOutputStream baos = new ByteArrayOutputStream();
				BufferedOutputStream out = new BufferedOutputStream(baos);
				int size;
				byte[] buffer = new byte[2048];
				while ((size = in.read(buffer, 0, buffer.length)) != -1) {
					out.write(buffer, 0, size);
				}

				if (entry != null)
					in.closeEntry();
				if (out != null) {
					out.close();
				}
				if (baos != null) {
					baos.close();
				}
				contentMap.put(entry.getName(), baos.toByteArray());

				// BufferedReader br = new BufferedReader(new InputStreamReader(in));
				// StringBuffer sb = new StringBuffer();
				// String line;
				// while ((line = br.readLine()) != null) {
				// sb.append(line)/*.append("\n")*/;
				// }
				// stringList.add(sb.toString());
				// contentMap.put(entry.getName(), sb.toString());
			}
		} catch (IOException e) {
			logger.error(e.toString(), e);
		} finally {
			try {
				if (fis != null) {
					fis.close();
				}
				if (bis != null) {
					bis.close();
				}
				if (in != null) {
					in.close();
				}
			} catch (IOException e) {
				logger.error(e.toString(), e);
			}
		}
		return contentMap;
	}

	private HashMap<String, String> unzipStream(InputStream iStream) {
		ArrayList<String> stringList = new ArrayList<String>();
		ArrayList<String> filenames = new ArrayList<String>();
		HashMap<String, String> contentMap = new HashMap<String, String>();

		BufferedInputStream bis = null;
		ZipInputStream in = null;
		try {
			bis = new BufferedInputStream(iStream);
			in = new ZipInputStream(bis);
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
				contentMap.put(entry.getName(), sb.toString());
			}
		} catch (IOException e) {
			logger.error(e.toString(), e);
		} finally {
			try {
				if (bis != null) {
					bis.close();
				}
				if (in != null) {
					in.close();
				}
			} catch (IOException e) {
				logger.error("Error closing zip input stream");
			}
		}

		return contentMap;
	}

	/**
	 * Sets the namespace of all Elements within Element root to Namespace ns
	 * 
	 * @param root
	 * @param ns
	 * @return
	 */
	@SuppressWarnings("unchecked")
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

	private Document getMarcModsLoss(Document marcDoc, Document modsDoc) {

		Element record = marcDoc.getRootElement();
		if (record == null) {
			return null;
		}

		Document missingElementsDoc = new Document(new Element("Lost-in-MarcMods-Conversion"));
		String modsString = CommonUtils.getStringFromDocument(modsDoc, encoding);
		// modsString = modsString.replaceAll("\"", "");

		Iterator<Content> descendant = record.getDescendants();
		while (descendant.hasNext()) {
			Element ele = null;
			Object obj = descendant.next();
			if (obj instanceof Element) {
				ele = (Element) obj;
				String marcContent = ele.getText();
				if (marcContent != null && !marcContent.isEmpty()) {
					try {
						CharSequence cs = marcContent.trim().subSequence(0, marcContent.trim().length() - 1);
						marcContent = cs.toString().trim();
						if (modsString.contains(marcContent)) {
							// marc field is contained in the mods doc
						} else {
							Element parentElement = ele.getParentElement();
							if (parentElement != null && parentElement != record) {
								// The element has a parent that is not the root element, which we should log as well
								Element parentClone = (Element) parentElement.clone();
								parentClone.removeContent();
								missingElementsDoc.getRootElement().addContent(parentClone);
								parentClone.addContent((Element) ele.clone());
							} else {
								missingElementsDoc.getRootElement().addContent((Element) ele.clone());
							}
						}
					} catch (IndexOutOfBoundsException e) {
						continue;
					}
				}

			}
		}
		return missingElementsDoc;
	}

	public static void main(String[] args) throws PreferencesException, WriteException {
		CSICMixedImport converter = new CSICMixedImport();
		converter.prefs = new Prefs();

		try {
			converter.prefs.loadPrefs("/opt/digiverso/goobi/rulesets/rulesetCSIC.xml");
		} catch (PreferencesException e) {
			logger.error(e.getMessage(), e);
		}

		converter.setImportFolder("output/");
		List<Record> records = new ArrayList<Record>();
		if (!converter.exportFolder.isDirectory()) {
			logger.warn("No export directory found. Aborting");
			return;
		}

		// for (File file : converter.exportFolder.listFiles(XmlFilter)) {

		// converter.createFileformat(file);
		File file = new File("/mnt/csic/0017_FACN/000009800_9800001020.xml");
		converter.setFile(file);
		records.addAll(converter.generateRecordsFromFile());
		// }

		List<ImportObject> results = converter.generateFiles(records);

		for (ImportObject record : results) {
			System.out.println(record.getProcessTitle() + " \t \t " + record.getImportReturnValue());
		}
	}

	// private Document getModsMetsLoss(Document modsDoc, Document metsDoc) {
	//
	// }

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
	public static FilenameFilter pdfFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			if (name.endsWith("pdf") || name.endsWith("PDF")) {
				validImage = true;
			}

			return validImage;
		}
	};
	public static FilenameFilter MetsFilter = new FilenameFilter() {
		@Override
		public boolean accept(File dir, String name) {
			boolean validImage = false;
			if (name.endsWith("XML") || name.endsWith("xml")) {
				validImage = true;
			}

			return validImage;
		}
	};
	// Filters for file searches
	public static FileFilter DirFilter = new FileFilter() {
		public boolean accept(File file) {
			return file.isDirectory();
		}
	};

	@Override
	public List<Record> generateRecordsFromFilenames(List<String> filenames) {

		// String filesToImport = "Files to import:";
		// for (String record : filenames) {
		// filesToImport += ("\n" + record);
		// }
		// System.out.println(filesToImport);

		ArrayList<Record> recordList = new ArrayList<Record>();
		for (String filename : filenames) {
			if (filename.contentEquals("Dummy")) {
				continue;
			}
			String[] parts = filename.split("::");
			if (parts == null || parts.length != 2) {
				// return recordList;
				continue;
			}
			String projectName = parts[0].trim();
			String fileName = parts[1].trim();
			File projectDir = new File(exportFolder, projectName);
			if (projectDir.isDirectory()) {
				File xmlDir = projectDir;
				File[] subDirs = projectDir.listFiles(MetsDirFilter);
				if (subDirs != null && subDirs.length > 0) {
					xmlDir = subDirs[0];
				}
				File file = new File(projectDir, fileName);
				importFile = file;
				List<Record> tempList = generateRecordsFromFile();
				if (tempList != null) {
					recordList.addAll(tempList);
				}
			}
		}
		// String imports = "Files to import:";
		// for (Record record : recordList) {
		// imports += ("\n" + record.getId());
		// }
		// System.out.println(imports);
		return recordList;
	}

	@Override
	public List<ImportProperty> getProperties() {
		// TODO Auto-generated method stub
		return null;
	}

	// @Override
	// public List<String> getAllFilenames() {
	// List<String> answer = new ArrayList<String>();
	// String folder = "/mnt/csic/0008_PCTN";
	// File f = new File(folder);
	// if (f.exists() && f.isDirectory()) {
	// String[] files = f.list();
	// for (String file : files) {
	// answer.add(file);
	// }
	// Collections.sort(answer);
	// }
	// return answer;
	// }

	@Override
	public List<String> getAllFilenames() {
		ArrayList<String> projectList = new ArrayList<String>(projectsCollectionsMap.keySet());
		ArrayList<String> filenameList = new ArrayList<String>();
		// filenameList.add("Dummy");
		// filenameList.add(exportFolder.getAbsolutePath());
		try {
			for (String project : projectList) {
				File projectDir = new File(exportFolder, project);
				if (projectDir.isDirectory()) {
					File xmlDir = projectDir;
					File[] subDirs = projectDir.listFiles(MetsDirFilter);
					if (subDirs != null && subDirs.length > 0) {
						xmlDir = subDirs[0];
					}
					// filenameList.add(xmlDir.getAbsolutePath());
					File[] fileList = projectDir.listFiles(MetsFilter);
					if (fileList != null && fileList.length > 0) {
						for (File file : fileList) {
							filenameList.add(project + "::\t" + file.getName());
							// filenameList.add(file.getAbsolutePath());
						}
					}
				}
			}
		} catch (Exception e) {
			filenameList.add("ERROR: " + e.getMessage());
			return filenameList;
		} catch (Error e) {
			filenameList.add("ERROR: " + e.getMessage());
			return filenameList;
		}
		Collections.sort(filenameList);
		return filenameList;
	}

	private boolean splitPdf(File pdfFile, File destDir) {

		if (pdfFile == null || !pdfFile.isFile()) {
			return false;
		}

		if (destDir == null || !destDir.exists()) {
			destDir.mkdirs();
		}

		PdfExtractor extractor = new PdfExtractor();

		return extractor.extractPdfs(pdfFile, destDir, null);

	}

	@Override
	public void deleteFiles(List<String> selectedFilenames) {
		// TODO Auto-generated method stub

	}

	@Override
	public List<DocstructElement> getCurrentDocStructs() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String deleteDocstruct() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String addDocstruct() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public List<String> getPossibleDocstructs() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public DocstructElement getDocstruct() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void setDocstruct(DocstructElement dse) {
		// TODO Auto-generated method stub

	}

	// Filters for file searches
	public static FileFilter MetsDirFilter = new FileFilter() {
		public boolean accept(File file) {
			if (file.isDirectory() && file.getName().toLowerCase().contains("mets")) {
				return true;
			}
			return false;
		}
	};
}
