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
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;

import net.xeoh.plugins.base.annotations.PluginImplementation;

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
import org.jdom.Document;
import org.jdom.Element;
import org.jdom.JDOMException;
import org.jdom.Namespace;
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
import ugh.dl.Person;
import ugh.dl.Prefs;
import ugh.dl.Reference;
import ugh.exceptions.DocStructHasNoTypeException;
import ugh.exceptions.MetadataTypeNotAllowedException;
import ugh.exceptions.PreferencesException;
import ugh.exceptions.ReadException;
import ugh.exceptions.TypeNotAllowedAsChildException;
import ugh.exceptions.TypeNotAllowedForParentException;
import ugh.exceptions.WriteException;
import ugh.fileformats.mets.MetsMods;
import de.intranda.goobi.plugins.utils.DocTypeConfiguration;
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
    private static final String VERSION = "1.1.20141121";
    private static final String XSLT_PATH = ConfigMain.getParameter("xsltFolder") + "MARC21slim2MODS3.xsl";
    public static final String MODS_MAPPING_FILE = ConfigMain.getParameter("xsltFolder") + "mods_map.xml";
    private static final String TEMP_DIRECTORY = ConfigMain.getParameter("tempfolder");
    public final boolean writeCurrentNoToMultiVolume = (ConfigPlugins.getPluginConfig(this).getBoolean("writeCurrentNoToMultiVolume", false));
    public final boolean writeCurrentNoSortingToMultiVolume = (ConfigPlugins.getPluginConfig(this).getBoolean("writeCurrentNoSortingToMultiVolume",
            false));
    public final boolean useSquareBracketsForVolume = (ConfigPlugins.getPluginConfig(this).getBoolean("useSquareBracketsForVolume", false));
    public final boolean addVolumeNoToTitle = (ConfigPlugins.getPluginConfig(this).getBoolean("addVolumeNoToTitle", false));

    // Namespaces
    private Namespace mets;

    private Prefs prefs;
    private String data = "";
    private File importFile = null;
    private String importFolder = "/output";
    private DocTypeConfiguration docTypeConfig;
    private Map<String, VolumeInfo> recordMap = new HashMap<String, VolumeInfo>();
    private Map<String, String> projectsCollectionsMap = new HashMap<String, String>();
    private Map<String, Integer> pageVolumeMap = new HashMap<String, Integer>();
    private HashMap<String, Boolean> idMap = new HashMap<String, Boolean>(); // maps to true all records with reoccuring ids (PPNs)
    private String currentIdentifier;
    private String currentTitle;
    private String currentAuthor;
    private String identifierSuffix;
    private List<String> currentCollectionList;
    private String encoding = "utf-8";
    private ArrayList<File> imageDirs = new ArrayList<File>();
    private ArrayList<File> pdfFiles = new ArrayList<File>();;
    public String currentPieceDesignation;
    public int currentVolume = 1;
    public int totalVolumes = 1;
    private String projectName;
    private Record currentRecord;
    private String dsAnchorType = null;
    private String dsType = null;
    private List<String> itemTitleList = new ArrayList<String>();

    /**
     * Directory containing the image files (possibly in TIFF/JPEG subfolders)
     */
    private final boolean deleteOriginalImages = ConfigPlugins.getPluginConfig(this).getBoolean("deleteOriginalImages", true);
    private final boolean deleteTempFiles = ConfigPlugins.getPluginConfig(this).getBoolean("deleteTempFiles", false);
    private final boolean logConversionLoss = ConfigPlugins.getPluginConfig(this).getBoolean("logConversionLoss", false);
    private final boolean copyImages = ConfigPlugins.getPluginConfig(this).getBoolean("copyImages", true);
    private final boolean copyPdfs = ConfigPlugins.getPluginConfig(this).getBoolean("copyPdfs", true);
    private final boolean updateExistingRecords = ConfigPlugins.getPluginConfig(this).getBoolean("updateExistingRecords", true);
    private final boolean relatedSeriesIsAnchor = ConfigPlugins.getPluginConfig(this).getBoolean("relatedSeriesIsAnchor", false);
    public final File exportFolder = new File(ConfigPlugins.getPluginConfig(this).getString("importFolder", "/opt/digiverso/ftp-import/"));
    public final String projectIdentifierTitle = (ConfigPlugins.getPluginConfig(this).getString("projectIdentifier", "projectIdentifier"));
    public File sourceFolder = null;
    public File logFolder = new File("/opt/digiverso/logs/CSIC");
    public boolean archiveImport = false;


    // private File exportFolder = new File("example");

    public CSICMixedImport() {
        
        docTypeConfig = new DocTypeConfiguration(ConfigPlugins.getPluginConfig(this), null);

        List<String> projectList = ConfigPlugins.getPluginConfig(this).getList("project[@name]");
        List<String> collectionList = ConfigPlugins.getPluginConfig(this).getList("project[@collection]");

        for (int i = 0; i < projectList.size(); i++) {
            String projectName = projectList.get(i);
            String collectionName = collectionList.get(i);
            projectsCollectionsMap.put(projectName, collectionName);
        }

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
                archiveImport = r.getId().startsWith("CSICAR");
                String idNumber = r.getId().split("_")[0].replaceAll("\\D", "");
                VolumeInfo info =
                        new VolumeInfo(idNumber, 1, 1, getPieceDesignation(imageDirs.get(0).getName()), imageDirs.get(0), pdfFile, identifierSuffix,
                                projectName);
                recordMap.put(r.getId(), info);
                if (idMap.get(idNumber) == null) {
                    idMap.put(idNumber, false);
                } else {
                    idMap.put(idNumber, true);
                }
                logger.debug("Adding record " + r.getId() + " to recordmap");
            }
        } else {
            int counter = 1;
            Collections.sort(imageDirs, new ProcessFileComparator());
            ArrayList<String> volumeList = new ArrayList<String>();

            String idNumber = r.getId().split("_")[0].replaceAll("\\D", "");
            if (idMap.get(idNumber) == null) {
                idMap.put(idNumber, false);
            } else {
                idMap.put(idNumber, true);
            }

            if (archiveImport) {
                VolumeInfo info = new VolumeInfo(idNumber, 1, 1, "", imageDirs, pdfFiles, "", projectName);
                recordMap.put(r.getId(), info);
                records.add(r);
            } else {
                for (File imageDir : imageDirs) {

                    String mySuffix = null;
                    if (imageDir.getName().contains("_V")) {
                        String volumeString = imageDir.getName().substring(imageDir.getName().lastIndexOf("_V"));
                        mySuffix = volumeString.substring(1);
                        // String volumeNoString = mySuffix.replaceAll("\\D", "");
                        // if (volumeNoString != null && !volumeNoString.isEmpty()) {
                        // counter = Integer.valueOf(volumeNoString);
                        // }
                        if (volumeList.contains(mySuffix)) {
                            mySuffix = null;
                        } else {
                            volumeList.add(mySuffix);
                        }
                    }

                    // create one new record for each image directory
                    Record rec = new Record();
                    if (mySuffix == null) {
                        mySuffix = "V" + volumeNumberFormat.format(counter);
                        while (volumeList.contains(mySuffix)) {
                            counter++;
                            mySuffix = "V" + volumeNumberFormat.format(counter);
                        }
                        volumeList.add(mySuffix);
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
                    VolumeInfo info =
                            new VolumeInfo(idNumber, counter, imageDirs.size(), getPieceDesignation(imageDir.getName()), imageDir, pdfFile, suffix,
                                    projectName);
                    recordMap.put(rec.getId(), info);
                    logger.debug("Adding record " + rec.getId() + " to recordmap");
                    // System.out.println("Volume " + counter + " = " + imageDir.getName());
                    counter++;
                }
            }
        }
        return records;
    }

    private String getPieceDesignation(String name) {

        if (name.startsWith("M_")) {
            name = name.substring(2);
        }

        String[] parts = name.split("_");
        int last = parts.length - 1;
        if (parts.length > 2) {
            return parts[last - 1];
        } else if (parts[last].startsWith("V")) {
            return null;
        } else {
            return parts[last];
        }

    }

    /**
     * 
     * 
     * @return
     */
    public Fileformat convertData() {
        if (data == null || data.isEmpty()) {
            logger.warn("Attempting to convert empty data. Aborting.");
            return null;
        }

        itemTitleList = new ArrayList<String>();
        Document marcDoc = null;
        Document doc = null;
        Fileformat innerff = null;
        try {
            // CREATE FILEFORMAT FROM MARC RECORD
            doc = CommonUtils.getDocumentFromString(data);
            marcDoc = getMarcDocument(doc, true);
            String marcString = getStringFromDocument(marcDoc, encoding);
            innerff = convertData(marcString);

            if (!deleteTempFiles && sourceFolder != null) {
                CommonUtils.writeTextFile(marcString, new File(sourceFolder, "marcDoc.xml"), encoding, false);
            }
        } catch (IOException e) {
            logger.error(e.toString(), e);
        }

        doc = swapStructData(doc);
        if (archiveImport) {
            doc = createArchiveStructData(doc);
            try {
                CommonUtils.getFileFromDocument(new File(sourceFolder, "metsDoc.xml"), doc);
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        } else {
            doc = replaceStructData(doc);
            try {
                CommonUtils.getFileFromDocument(new File(sourceFolder, "metsDoc.xml"), doc);
            } catch (IOException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }

        // CREAGE FILEFORMAT FROM MODS DOC
        Fileformat outerff = null;
        File tempFile = new File(TEMP_DIRECTORY, "temp.xml");
        try {
            if (!archiveImport) {
                CommonUtils.getFileFromDocument(tempFile, doc);
                outerff = new MetsMods(prefs);
                outerff.read(tempFile.getAbsolutePath());
                compareFileFormats(innerff, outerff);
                removeOtherVolumes(outerff);
            } else {
                innerff.write(tempFile.getAbsolutePath());
                Document innerDoc = CommonUtils.getDocumentFromFile(tempFile);
                doc = replaceXmlData(doc, innerDoc);
                CommonUtils.getFileFromDocument(tempFile, doc);
                outerff = new MetsMods(prefs);
                outerff.read(tempFile.getAbsolutePath());
                nameItems(outerff);
                createPageLinks(outerff.getDigitalDocument().getLogicalDocStruct());
            }
        } catch (PreferencesException e) {
            logger.error(e.toString());
        } catch (ReadException e) {
            logger.error(e.toString());
        } catch (IOException e) {
            logger.error(e.toString());
        } catch (WriteException e) {
            logger.error(e.toString());
        } catch (JDOMException e) {
            logger.error(e.toString());
        }

        if (tempFile.exists()) {
            tempFile.delete();
        }

        return outerff;
    }

    private void createPageLinks(DocStruct logicalDocStruct) {
        if(logicalDocStruct.getType().isAnchor()) {
            logicalDocStruct = logicalDocStruct.getAllChildren().get(0);
        }
        List<DocStruct> itemList = null;
        itemList = getAllDescendants(logicalDocStruct, prefs.getDocStrctTypeByName("SimpleDocument"));
        for (DocStruct docStruct : itemList) {
            List<Reference> referenceList = docStruct.getAllToReferences();
            for (Reference reference : referenceList) {
                logicalDocStruct.addReferenceTo(reference.getTarget(), reference.getType());
            }
        }

    }

    private void nameItems(Fileformat ff) {
        List<DocStruct> itemList;
        try {
            itemList = getAllDescendants(ff.getDigitalDocument().getLogicalDocStruct(), prefs.getDocStrctTypeByName("SimpleDocument"));
        } catch (PreferencesException e1) {
            logger.error("Logical topStruct has no children");
            return;
        }
        int count = 0;
        DecimalFormat formatter = new DecimalFormat("00");
        for (DocStruct ds : itemList) {
            try {
                String title = itemTitleList.get(count);
                Metadata md = new Metadata(prefs.getMetadataTypeByName("TitleDocMain"));
                md.setValue(title);
                ds.addMetadata(md);
            } catch (MetadataTypeNotAllowedException e) {
                logger.error("Failed to add title to item " + count);
            }
            try {
                String idDitital = currentIdentifier + "_" + formatter.format(count + 1);
                Metadata md = new Metadata(prefs.getMetadataTypeByName("CatalogIDDigital"));
                md.setValue(idDitital);
                ds.addMetadata(md);
            } catch (MetadataTypeNotAllowedException e) {
                logger.error("Failed to add id to item " + count);
            }
            count++;
        }

    }

    private List<DocStruct> getAllDescendants(DocStruct logicalDocStruct, DocStructType dsType) {
        List<DocStruct> dsList = new ArrayList<DocStruct>();
        List<DocStruct> children = logicalDocStruct.getAllChildren();
        if (children != null && !children.isEmpty()) {
            for (DocStruct ds : children) {
                if (dsType == null || ds.getType().equals(dsType)) {
                    dsList.add(ds);
                }
                dsList.addAll(getAllDescendants(ds, dsType));
            }
        }
        return dsList;
    }

    private void removeOtherVolumes(Fileformat outerff) throws PreferencesException {

        // remove logical structures
        DocStruct topStruct = outerff.getDigitalDocument().getLogicalDocStruct();
        DocStruct validVolume = topStruct;
        ArrayList<DocStruct> invalidDocStructs = new ArrayList<DocStruct>();
        List<DocStruct> logStructs = topStruct.getAllChildren();
        if (logStructs != null && !logStructs.isEmpty()) {
            Collections.sort(logStructs, new VolumeComparator());
        }
        if (topStruct.getType().isAnchor() && logStructs != null && logStructs.size() > 1) {
            for (int i = 1; i <= logStructs.size(); i++) {
                if (i != currentVolume) {
                    invalidDocStructs.add(logStructs.get(i - 1));
                    // topStruct.removeChild(topStruct.getAllChildren().get(i-1));
                } else {
                    validVolume = logStructs.get(i - 1);
                }
            }
            for (DocStruct docStruct : invalidDocStructs) {
                topStruct.removeChild(docStruct);
            }

        } else if (topStruct.getType().isAnchor()) {
            validVolume = topStruct.getAllChildren().get(0);
        }

        // clean references
        if (validVolume != null) {
            List<Reference> references = validVolume.getAllToReferences();
            if (references != null) {
                List<DocStruct> targets = new ArrayList<DocStruct>();
                for (Reference reference : references) {
                    targets.add(reference.getTarget());
                }
                for (DocStruct target : targets) {
                    validVolume.removeReferenceTo(target);
                }
            }
        }

        // remove physical structures
        DocStruct bookStruct = outerff.getDigitalDocument().getPhysicalDocStruct();
        DocStruct collectionStruct = null;

        while (bookStruct.getAllChildren() != null && !bookStruct.getAllChildren().get(0).getType().getName().contentEquals("page")) {
            collectionStruct = bookStruct;
            bookStruct = bookStruct.getAllChildren().get(0);
        }

        //remove superfluous books
        if (collectionStruct != null) {
            ArrayList<DocStruct> invalidBooks = new ArrayList<DocStruct>();
            List<DocStruct> physStructs = collectionStruct.getAllChildren();
            Collections.sort(physStructs, new VolumeComparator());
            if (physStructs.size() > 1) {
                for (int i = 1; i <= physStructs.size(); i++) {
                    if (i != currentVolume) {
                        invalidBooks.add(physStructs.get(i - 1));
                        // topStruct.removeChild(topStruct.getAllChildren().get(i-1));
                    } else {
                        bookStruct = physStructs.get(i - 1);
                    }
                }
                for (DocStruct docStruct : invalidBooks) {
                    collectionStruct.removeChild(docStruct);
                }
            }
        }

        //add metadata to bookStruct
        DocStruct origBook = outerff.getDigitalDocument().getPhysicalDocStruct();
        if (origBook != bookStruct && origBook.getAllMetadata() != null) {
            for (Metadata md : origBook.getAllMetadata()) {
                Metadata newMd;
                try {
                    newMd = new Metadata(md.getType());
                    newMd.setValue(md.getValue());
                    bookStruct.addMetadata(newMd);
                } catch (MetadataTypeNotAllowedException e) {
                    logger.error("Unable to add metadata " + md.getType().getName() + " to physical DocStruct");
                }
            }
        }
        outerff.getDigitalDocument().setPhysicalDocStruct(bookStruct);

        for (DocStruct page : bookStruct.getAllChildren()) {
            validVolume.addReferenceTo(page, "logical_physical");
        }
    }

    private void compareFileFormats(Fileformat innerff, Fileformat outerff) {

        try {
            DocStruct innerLogStruct = innerff.getDigitalDocument().getLogicalDocStruct();
            DocStruct outerLogStruct = outerff.getDigitalDocument().getLogicalDocStruct();
            List<DocStruct> innerChildren = innerLogStruct.getAllChildren();
            List<DocStruct> outerChildren = outerLogStruct.getAllChildren();

            if (!archiveImport) {
                DocStructType innerAnchorType = null;
                DocStructType innerTopStructType = null;
                if (innerLogStruct.getType().isAnchor()) {
                    innerAnchorType = innerLogStruct.getType();
                    innerTopStructType = innerChildren.get(0).getType();
                } else {
                    innerTopStructType = innerLogStruct.getType();
                }

                if (innerAnchorType != null) {
                    if (outerChildren == null || outerChildren.isEmpty()) {
                        // We need to import the inner anchor
                        outerChildren = new ArrayList<DocStruct>();
                        DocStructType tempType = outerLogStruct.getType();
                        outerChildren.add(outerLogStruct.copy(false, false));
                        outerLogStruct = innerLogStruct.copy(false, false);
                        outerLogStruct.setType(tempType);
                        outerLogStruct.addChild(outerChildren.get(0));
                        outerff.getDigitalDocument().setLogicalDocStruct(outerLogStruct);
                    }
                    outerLogStruct.setType(innerAnchorType);
                    // copy metadata to anchor
                    copyAllMetadata(innerLogStruct, outerLogStruct);
                    // copy metadata to children
                    for (DocStruct ds : outerChildren) {
                        ds.setType(innerTopStructType);
                        copyAllMetadata(innerChildren.get(0), ds);
                    }
                } else {
                    // no inner anchor
                    if (outerChildren != null && !outerChildren.isEmpty()) {
                        if (outerChildren.size() > 1) {
                            // This shouldn't happen
                            logger.error("More than one outer volume, but no inner anchor");
                        } else {
                            // Remove the outer anchor
                            outerLogStruct = outerChildren.get(0).copy(false, false);
                            outerff.getDigitalDocument().setLogicalDocStruct(outerLogStruct);
                        }
                    }
                    outerLogStruct.setType(innerTopStructType);
                    // now copy metadata
                    copyAllMetadata(innerLogStruct, outerLogStruct);
                }
            } else {
                //archive import

            }

            // Now copy the physical metadata
            List<DocStruct> bookList = new ArrayList<DocStruct>();
            bookList.add(outerff.getDigitalDocument().getPhysicalDocStruct());
            while (bookList.size() > 0 && bookList.get(0).getType().getName().contentEquals("Collection")) {
                List<DocStruct> children = bookList.get(0).getAllChildren();
                if (children != null && !children.isEmpty()) {
                    bookList = children;
                } else {
                    // This shouldn't happen
                    logger.error("No BoundBook found in physicalDocument");
                    break;
                }
            }
            for (DocStruct ds : bookList) {
                copyAllMetadata(innerff.getDigitalDocument().getPhysicalDocStruct(), ds);
            }

        } catch (PreferencesException e) {
            logger.error(e);
        } catch (TypeNotAllowedAsChildException e) {
            logger.error(e);
        }
    }

    /**
     * Removes and childen and metadata not allowed for this docStructType
     * 
     * @param docStruct
     */
    private void verifyDocStructIntegrity(DocStruct docStruct) {
        if (docStruct.getAllChildren() != null) {
            ArrayList<DocStruct> childrenToRemove = new ArrayList<DocStruct>();
            for (DocStruct child : docStruct.getAllChildren()) {
                if (!docStruct.isDocStructTypeAllowedAsChild(child.getType())) {
                    logger.warn("Removing child " + child.getType().getName() + " from DocStruct " + docStruct.getType().getName());
                    childrenToRemove.add(child);
                    // docStruct.removeChild(child);
                }
            }
            for (DocStruct docStruct2 : childrenToRemove) {
                docStruct.removeChild(docStruct2);
            }
        }
        if (docStruct.getAllMetadata() != null) {
            ArrayList<Metadata> metadataToRemove = new ArrayList<Metadata>();
            HashMap<MetadataType, Boolean> existingMetadataMap = new HashMap<MetadataType, Boolean>();
            for (Metadata metadata : docStruct.getAllMetadata()) {
                MetadataType type = metadata.getType();
                boolean isAllowed = false;
                for (MetadataType mdType : docStruct.getType().getAllMetadataTypes()) {
                    if (mdType.getName().contentEquals(type.getName())) {
                        isAllowed = true;
                        if (docStruct.getType().getNumberOfMetadataType(mdType).contentEquals("1o") && existingMetadataMap.get(mdType) != null) {
                            // a metadata of this type already exists, although only one instance is permitted. Delete this instance
                            isAllowed = false;
                        } else {
                            existingMetadataMap.put(mdType, true);
                        }

                    }

                }

                if (!isAllowed) {
                    // if (!docStruct.getType().isMDTypeAllowed(type)) {
                    logger.warn("Removing metadata " + metadata.getType().getName() + " from DocStruct " + docStruct.getType().getName());
                    metadataToRemove.add(metadata);
                    // docStruct.removeMetadata(metadata);
                }
            }
            for (Metadata metadata : metadataToRemove) {
                docStruct.removeMetadata(metadata);
            }
        }
    }

    /**
     * 
     * generate mets files and copy image files from record list
     * 
     */
    @Override
    public List<ImportObject> generateFiles(List<Record> records) {
        ArrayList<ImportObject> ret = new ArrayList<ImportObject>();

        for (Record r : records) {
            currentRecord = r;
            logger.info("Processing " + r.getId());
            // Data conversion
            data = r.getData();
            VolumeInfo info = recordMap.get(r.getId());
            // VolumeInfo info = (VolumeInfo)CommonUtils.getFromMap(recordMap, r.getId());
            if (info == null) {
                logger.error("Unable to find information to that record");
                continue;
            }
            currentIdentifier = info.identifier;
            currentPieceDesignation = info.pieceDesignation;
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
            // correctId(ff);
            ImportObject io = new ImportObject();

            if (ff != null) {

                // add collection as metadata

                // writing converted data into Import("temp") folder
                try {
                    MetsMods mm = new MetsMods(prefs);
                    mm.setDigitalDocument(ff.getDigitalDocument());
                    String fileName = getImportFolder() + getProcessTitle();
                    addProject(ff, info.projectName);

                    logger.debug("Writing '" + fileName + "'...");
                    mm.write(fileName);
                    logger.debug("copying image files from image directories...");
                    copyImageFiles(info.imageDirs);
                    copyPdfs(info.pdfFiles);
                    io.setProcessTitle(getProcessTitle().replace(".xml", ""));
                    io.setMetsFilename(fileName);
                    io.setImportReturnValue(ImportReturnValue.ExportFinished);

                    Prozesseigenschaft property = new Prozesseigenschaft();
                    property.setTitel(projectIdentifierTitle);
                    property.setWert(info.projectName);
                    ArrayList<Prozesseigenschaft> propertyList = new ArrayList<Prozesseigenschaft>();
                    propertyList.add(property);
                    io.setProcessProperties(propertyList);

                    if (importFile != null && importFile.isFile() && sourceFolder != null) {
                        try {
                            CommonUtils.moveFile(importFile, new File(sourceFolder, importFile.getName()), true);
                            // importFile.renameTo(new File(sourceFolder, importFile.getName()));
                        } catch (IOException e) {
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
        projectName = getActualProjectName(projectName);
        try {
            DocStruct topStruct = ff.getDigitalDocument().getLogicalDocStruct();
            if (topStruct.getAllMetadataByType(prefs.getMetadataTypeByName("ProjectIdentifier")) == null
                    || topStruct.getAllMetadataByType(prefs.getMetadataTypeByName("ProjectIdentifier")).isEmpty()) {
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

        projectName = null;
        List<Record> origRecordList = retrieveOriginalRecordsFromFile();
        List<Record> recordList = generateRecordsForImport(origRecordList);

        return recordList;
    }

    private List<Record> generateRecordsForImport(List<Record> origRecordList) {
        List<Record> recordList = new ArrayList<Record>();
        HashMap<Record, File> updateRecordMap = new HashMap<Record, File>();

        for (Record record : origRecordList) {

            identifierSuffix = null;
            String searchString = parseImagefolder(record); // get the image folders corresponding to this record, plus an additional process
            logger.debug("Project name is " + projectName);
            record.setId(searchString); // identifer if necessary
            List<Record> childRecords = generateRecords(record);

            for (Record childRecord : childRecords) {
                File oldFile = searchForExistingData(childRecord);
                if (oldFile != null) {
                    if (updateExistingRecords) {
                        logger.info("Found existing record. Updating.");
                        updateRecordMap.put(childRecord, oldFile);
                    } else {
                        Helper.setFehlerMeldung("Cannot import record " + record.getId() + " : A process with this title already exists.");
                    }
                } else {
                    recordList.add(childRecord);
                }
            }

        }

        if (recordList.size() > 0 && importFile != null) {
            logger.info("Extracted " + recordList.size() + " records from '" + importFile.getName() + "'.");
        } else if (updateRecordMap.size() > 0 && importFile != null) {
            logger.info("Updating " + updateRecordMap.size() + " records from '" + importFile.getName() + "'.");
        } else {
            logger.error("No record extracted from importFile");
        }

        for (Record record : updateRecordMap.keySet()) {
            if (!updateOldRecord(record, updateRecordMap.get(record))) {
                Helper.setFehlerMeldung("Error updating record " + record.getId());
            } else {
                Helper.setMeldung("Updated process " + record.getId());
            }
        }
        return recordList;
    }

    private List<Record> retrieveOriginalRecordsFromFile() {

        List<Record> recordList = new ArrayList<Record>();
        HashMap<String, String> filteredRecordStrings = new HashMap<String, String>();
        int count = 0;

        if (importFile.getName().endsWith("zip")) {
            logger.info("Extracting zip archive");
            HashMap<String, byte[]> recordStrings = unzipFile(importFile);
            // Check all records first to see what's inside
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
                                logger.error(e);
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
                recordList.add(rec);
            }
        } else {
            logger.info("Importing single record file");
            InputStream input = null;
            StringWriter writer = null;
            try {
                logger.debug("loaded file: " + importFile.getAbsolutePath());
                String importFileName = importFile.getName();
                input = new FileInputStream(importFile);
                Record rec = new Record();
                writer = new StringWriter();
                IOUtils.copy(input, writer, encoding);
                rec.setData(writer.toString());
                rec.setId(importFileName.substring(0, importFileName.indexOf(".")));
                recordList.add(rec);
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
            }
        }
        return recordList;

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
        return title;
        // if (identifierSuffix != null && !identifierSuffix.isEmpty()) {
        // return title.replace(".xml", "_" + identifierSuffix + ".xml");
        // } else {
        // return title;
        // }
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
                    dsType = null;
                    dsAnchorType = null;
                    String typeOfResource = null;
                    boolean belongsToPeriodical = false;
                    boolean belongsToSeries = false;
                    boolean isManuscript = false;
                    boolean belongsToMultiVolume = false;

                    // handle TypeOfResource
                    List<Element> eleTypeOfResourceList = eleMods.getChildren("typeOfResource", null);
                    if (eleTypeOfResourceList != null) {
                        for (Element eleTypeOfResource : eleTypeOfResourceList) {
                            String resourceLabel = eleTypeOfResource.getAttributeValue("displayLabel");
                            if (resourceLabel != null && resourceLabel.contains("SE")) {
                                belongsToPeriodical = true;
                            }
                            if ("yes".equals(eleTypeOfResource.getAttributeValue("manuscript"))) {
                                isManuscript = true;
                            }
                            typeOfResource = eleTypeOfResource.getTextTrim();
                        }
                    }

                    // handle physicalDescription
                    List<Element> physicalDescriptionList = eleMods.getChildren("physicalDescription", null);
                    if (physicalDescriptionList != null) {
                        for (Element physDescr : physicalDescriptionList) {
                            List<Element> eleFormList = physDescr.getChildren("form", null);
                            if (eleFormList != null) {
                                for (Element eleForm : eleFormList) {
                                    if (eleForm.getAttribute("authority") != null && eleForm.getValue().contentEquals("Manuscrito")) {
                                        isManuscript = true;
                                    }
                                }
                            }
                        }
                    }
                    
                    // handle archive
                    List<Element> recordInfoList = eleMods.getChildren("recordInfo", null);
                    if (physicalDescriptionList != null) {
                        for (Element recordInfo : recordInfoList) {
                            List<Element> eleIdList = recordInfo.getChildren("recordIdentifier", null);
                            if (eleIdList != null) {
                                for (Element eleId : eleIdList) {
                                    String id = eleId.getTextTrim();
                                    if(id != null && id.startsWith("CSICAR")) {
                                        archiveImport = true;
                                    }
                                }
                            }
                        }
                    }

                    // handle relatedSeries
                    List<Element> eleRelatedSeriesList = eleMods.getChildren("relatedItem", null);
                    if (relatedSeriesIsAnchor && eleRelatedSeriesList != null) {
                        for (Element eleRelatedSeries : eleRelatedSeriesList) {

                            if (eleRelatedSeries != null && eleRelatedSeries.getAttribute("type") != null
                                    && eleRelatedSeries.getAttribute("type").getValue().contentEquals("series")) {
                                belongsToSeries = true;
                            }
                        }
                    }

                    if (idMap.get(currentIdentifier.replaceAll("\\D", "")) != null) {

                        if (idMap.get(currentIdentifier.replaceAll("\\D", "")) == true) {
                            belongsToMultiVolume = true;
                        } else if ((identifierSuffix != null && identifierSuffix.startsWith("V")) && ((!belongsToPeriodical && !belongsToSeries))) {
                            belongsToMultiVolume = true;
                        }
                        // This volume is part of a Series/Multivolume work
                        // if (!belongsToPeriodical && !belongsToSeries) {
                        // }
                    }
                    
                    boolean multipart = belongsToMultiVolume || belongsToPeriodical || belongsToSeries;

                    dsType = docTypeConfig.getDocType(typeOfResource, multipart, archiveImport);
                    dsAnchorType = docTypeConfig.getAnchorType(typeOfResource, multipart, archiveImport);

                    // remove unnecessary suffixes for everything but multivolumes
                    if (!belongsToMultiVolume) {
                        if (idMap.get(currentIdentifier.replaceAll("\\D", "")) != null && idMap.get(currentIdentifier.replaceAll("\\D", "")) == true) {
                            // need suffix
                        } else {
                            identifierSuffix = null;
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
                    logger.debug("Anchor type: " + dsAnchorType);
                    dsAnchor = dd.createDocStruct(prefs.getDocStrctTypeByName(dsAnchorType));
                    if (dsAnchor == null) {
                        logger.error("Could not create DocStructType " + dsAnchorType);
                    }
                    try {
                        dsAnchor.addChild(dsVolume);
                    } catch (TypeNotAllowedAsChildException e) {
                        logger.error("Could not attach " + dsAnchorType + " to anchor " + dsType);
                    }
                    dd.setLogicalDocStruct(dsAnchor);
                } else {
                    dd.setLogicalDocStruct(dsVolume);
                }

                DocStruct dsBoundBook = dd.createDocStruct(prefs.getDocStrctTypeByName("BoundBook"));
                dd.setPhysicalDocStruct(dsBoundBook);

                //get volume number of this item
                Integer volumeNo = ModsUtils.getNumberFromString(this.getCurrentSuffix());
                if (volumeNo == null) {
                    volumeNo = currentVolume;
                }

                // Collect MODS metadata
                ModsUtils.parseModsSection(this, dsVolume, dsAnchor, dsBoundBook, eleMods, volumeNo, currentPieceDesignation);
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

                if (logConversionLoss) {
                    try {
                        File marcLossFile = new File(logFolder, currentIdentifier + "_MarcLoss.xml");
                        Document lossDoc = getMarcModsLoss(doc, docMods);
                        CommonUtils.getFileFromDocument(marcLossFile, lossDoc);
                        File modsFile = new File(logFolder, currentIdentifier + "_Mods.xml");
                        CommonUtils.getFileFromDocument(modsFile, docMods);
                    } catch (IOException e) {
                        logger.error(e);
                    }
                }

                if (!deleteTempFiles) {
                    try {
                        File modsFile = new File(sourceFolder, "modsTemp.xml");
                        CommonUtils.getFileFromDocument(modsFile, docMods);
                    } catch (IOException e) {
                        logger.error(e);
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
                        //                        if (dsAnchor != null) {
                        //                            dsAnchor.addMetadata(mdCollection);
                        //                        }
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
    private File searchForExistingData(Record r) {
        String processTitle = r.getId();

        // For imports with wrong processTitle, correct it
        //        processTitle = processTitle.replace("000471130", "001100392");
        processTitle = processTitle.replace("001363255", "000884278");
        processTitle = processTitle.replace("00045898", "000045898");
        processTitle = processTitle.replace("0000045898", "000045898");
        //

        int index = processTitle.indexOf("_");
        String processId = processTitle;
        String processIdSuffix = "";
        String processIdVolume = "";
        if (index > 0 && index < processTitle.length()) {
            processId = processTitle.substring(0, index);
            processIdSuffix = processTitle.substring(index + 1);
            int vIndex = processIdSuffix.indexOf("V");
            if (vIndex > -1 && vIndex < processIdSuffix.length() - 2) {
                processIdVolume = processIdSuffix.substring(vIndex);
                if (processIdVolume.contains("_")) {
                    processIdVolume = processIdVolume.substring(0, processIdVolume.indexOf("_"));
                }
            }
        }
        String metsFilePath, processDataDirectory;
        ProzessDAO dao = new ProzessDAO();

        try {
            List<Prozess> processList = dao.search("from Prozess where titel LIKE '%" + processId + "%'");

            if (processList == null || processList.isEmpty()) {
                String id = processTitle.split("_")[0] + "_V00";
                processList = dao.search("from Prozess where titel LIKE '%" + id + "'");
            }

            if (processList != null && !processList.isEmpty()) {
                Prozess p = processList.get(0);
                if (processList.size() > 1) {
                    for (Prozess process : processList) {
                        if (process.getTitel().contains(processIdSuffix)) {
                            p = process;
                            break;
                        } else if (p.getTitel().contains(processIdVolume)) {
                            p = process;
                        }
                    }

                }

                VolumeInfo info = recordMap.get(r.getId());
                recordMap.remove(r.getId());
                p.setTitel(p.getTitel().split("_")[0] + "_" + processTitle);
                r.setId(p.getTitel());
                recordMap.put(r.getId(), info);
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

        currentRecord = record;
        VolumeInfo info = recordMap.get(record.getId());
        if (info == null) {
            logger.error("Unable to find information to that record");
            return false;
        }
        currentPieceDesignation = info.pieceDesignation;
        currentIdentifier = info.identifier;
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
        addProject(ff, info.projectName);
        // correctId(ff);
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

            // MetsMods mm = new MetsMods(prefs);
            // mm.setDigitalDocument(ff.getDigitalDocument());

            ff.write(fileName);
            copyImageFiles(info.imageDirs);
            copyPdfs(info.pdfFiles);
            // getting anchor file
            File importDir = new File(importFolder);
            if (!importDir.isDirectory()) {
                logger.warn("no hotfolder found. Cannot get anchor files");
            } else {

                File tempFolder = new File(importFolder, getProcessTitle().replace(".xml", ""));
                if (tempFolder.isDirectory()) {
                    CommonUtils.moveDir(tempFolder, oldMetaFile.getParentFile(), true);
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
        } finally {
            logger.trace("Deleting importFile");
            importFile.delete();
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
    private Document getMarcDocument(Document inDoc, boolean insertFakeMods) {
        Element marcRecord = null;
        Element eleMarc = null;
        // getting document elements
        Element root = inDoc.getRootElement();

        logger.debug("getting document elements");
        if (root != null) {
            if (root.getChildren() == null || root.getChildren().isEmpty()) {
                logger.error("No children found in root");
                return null;
            } else {
                try {
                    eleMarc = root.getChild("dmdSec", mets).getChild("mdWrap", mets).getChild("xmlData", mets).getChild("marc", null);
                    marcRecord = eleMarc.getChild("record", null);
                } catch (NullPointerException e) {
                    logger.error("No dmdSec or marcData found");
                    return null;
                }
            }
        }
        marcRecord.detach();
        if (insertFakeMods) {
            eleMarc.setName("mods");
            Element extension = new Element("extension");
            eleMarc.addContent(extension);
            Element eleGoobi = new Element("goobi");
            extension.addContent(eleGoobi);
            // Element fakeAnchorId = new Element("metadata");
            // fakeAnchorId.setAttribute("name", "CatalogIDDigital");
            // fakeAnchorId.setAttribute("anchorId", "true");
            // fakeAnchorId.setText("0000");
            // eleGoobi.addContent(fakeAnchorId);

        }
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
        // premis = root.getNamespace("premis");
        // if (premis != null)
        // logger.debug("Namespace premis: Prefix = " + premis.getPrefix() + ", uri = " + premis.getURI());
        // mix = root.getNamespace("mix");
        // if (mix != null)
        // logger.debug("Namespace mix: Prefix = " + mix.getPrefix() + ", uri = " + mix.getURI());
        // marc = root.getNamespace("marc");
        // if (marc != null)
        // logger.debug("Namespace marc: Prefix = " + marc.getPrefix() + ", uri = " + marc.getURI());
        // mods = root.getNamespace("mods");
        // if (mods != null)
        // logger.debug("Namespace mods: Prefix = " + mods.getPrefix() + ", uri = " + mods.getURI());
        // goobi = root.getNamespace("goobi");
        // if (goobi != null) {
        // logger.debug("Namespace goobi: Prefix = " + goobi.getPrefix() + ", uri = " + goobi.getURI());
        // } else {
        // // goobi = Namespace.getNamespace("goobi", null);
        // }
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
        String[] idParts = id.split("_");
        int first = 0;
        int last = idParts.length - 1;
        if (idParts == null || idParts.length == 0) {
            return null;
        }
        if (idParts[0].contentEquals("M") && idParts.length > 1) {
            first = 1;
        }
        identifier = idParts[first];

        if (idParts.length > first + 1) {
            if (idParts[last].startsWith("V")) {
                volumeIdentifier = idParts[last];
                last--;
            }
            for (int i = first + 1; i < last + 1; i++) {
                if (pieceDesignation == null) {
                    pieceDesignation = idParts[i];
                } else if (idParts[i] != null && !idParts[i].isEmpty()) {
                    pieceDesignation += ("_" + idParts[i]);
                }
            }
        }

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

            List<File> folders = Arrays.asList(folder.listFiles());
            File tiffDir = null, pdfDir = null;
            for (File file : folders) {
                if (file.isDirectory() && file.getName().toLowerCase().contentEquals("tiff")) {
                    logger.debug("found \"tiff\" directory in " + folder.getName());
                    tiffDir = file;
                }

                if (file.isDirectory() && file.getName().toLowerCase().contentEquals("pdf")) {
                    logger.debug("found \"pdf\" directory in " + folder.getName());
                    pdfDir = file;
                }
            }

            List<File> processFolders = Arrays.asList(folder.listFiles());
            List<File> tiffFolders = null;
            if (tiffDir != null) {
                tiffFolders = Arrays.asList(tiffDir.listFiles());
            }
            ArrayList<File> idImageDirs = new ArrayList<File>();
            ArrayList<File> idRecordFiles = new ArrayList<File>();
            // Get image dirs matching the identifier
            for (File file : processFolders) {
                if (file.isDirectory() && file.getName().contains(identifier)) {
                    idImageDirs.add(file);
                    logger.debug("found export folder " + file.getName() + " in " + folder.getAbsolutePath());
                } else if (file.isFile() && file.getName().toLowerCase().endsWith(".xml") && file.getName().contains(identifier)) {
                    idRecordFiles.add(file);
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
            } else if (idRecordFiles.size() == 1) {
                // there is only one record of this id, so get all matching imageDirs
                imageDirs = idImageDirs;
            } else {
                for (File dir : idImageDirs) {
                    if (pieceDesignation == null || dir.getName().contains("_" + pieceDesignation)) {
                        if (volumeIdentifier == null || dir.getName().contains("_" + volumeIdentifier)) {
                            imageDirs.add(dir);
                        }
                    }
                }
            }

            //if necessary, attempt to get volumeNumber from image dir
            if (pieceDesignation != null && volumeIdentifier == null && imageDirs.size() == 1) {
                String imageDirName = imageDirs.get(0).getName();
                int pieceDesignationStartPos = imageDirName.lastIndexOf(pieceDesignation);
                int pieceDesignationEndPos = pieceDesignationStartPos + pieceDesignation.length() + 1;
                if (pieceDesignationStartPos > 0 && pieceDesignationEndPos < imageDirName.length()) {
                    String volumeString = imageDirName.substring(pieceDesignationEndPos);
                    if (volumeString != null && !volumeString.isEmpty()) {
                        volumeIdentifier = volumeString;
                    }
                }
            }

            // sort imageDirs by name
            if (imageDirs != null && !imageDirs.isEmpty()) {
                Collections.sort(imageDirs);
            }

            if (idImageDirs.size() > imageDirs.size()) {
                // there is at least one other process with the same identifier. Add volume or pieceDesignation to this identifier
                if (volumeIdentifier != null && !volumeIdentifier.contentEquals("V00")) {
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

    private String getActualProjectName(String name) {
        if (name.contentEquals("0006_PMSC_GR_EEA")) {
            return "0006_PMSC";
        }
        return name;
    }

    /**
     * 
     * Copy the files in exportFolder corresponding to the current record into the importFolder
     * 
     * @param exportFolder
     */
    private void copyImageFiles(List<File> imageDirs) {

        if (!copyImages || imageDirs == null || imageDirs.isEmpty()) {
            logger.debug("No images to copy");
            return;
        }

        Collections.sort(imageDirs);

        // get temp dir
        File tempDir = new File(importFolder, getProcessTitle().replace(".xml", ""));
        File tempImageDir = new File(tempDir, "images");
        File tempTiffDir = new File(tempImageDir, getProcessTitle().replace(".xml", "") + "_tif");
        // File tempOrigDir = new File(tempImageDir, "orig_" + getProcessTitle().replace(".xml", "") + "_tif");
        tempTiffDir.mkdirs();

        // parse all image Files and write them into new Files in the import
        // directory
        List<File> images = new ArrayList<File>();
        //        Collections.sort(imageDirs);
        for (File dir : imageDirs) {
            images.addAll(Arrays.asList(dir.listFiles(ImageFilter)));
        }

        for (File imageFile : images) {
            try {
                String filename = imageFile.getName();
                if (!deleteOriginalImages) {
                    copyFile(imageFile, new File(tempTiffDir, filename));
                    logger.debug("Copying image " + filename);
                } else {
                    CommonUtils.moveFile(imageFile, new File(tempTiffDir, filename), true);

                }

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

    private void copyPdfs(List<File> pdfFiles) {

        if (!copyPdfs || pdfFiles == null || pdfFiles.isEmpty()) {
            logger.debug("No pdf to copy");
            return;
        }

        Collections.sort(pdfFiles);

        // get temp dir
        File tempDir = new File(importFolder, getProcessTitle().replace(".xml", ""));
        File tempOcrDir = new File(tempDir, "ocr");
        File tempPdfDir = new File(tempOcrDir, getProcessTitle().replace(".xml", "") + "_pdf");
        tempPdfDir.mkdirs();
        PdfExtractor extractor = new PdfExtractor();
        for (File pdfFile : pdfFiles) {
            try {
                splitPdf(pdfFile, tempPdfDir, extractor);
                if (deleteOriginalImages) {
                    pdfFile.delete();
                }
            } catch (Exception e) {
                logger.error(e.getMessage(), e);
            }
        }
    }

    @SuppressWarnings("unchecked")
    private Document createArchiveStructData(Document doc) {

        mets = doc.getRootElement().getNamespace("mets");

        Element physStruct = null;
        Element logStruct = null;
        List<Element> structMaps = doc.getRootElement().getChildren("structMap", mets);

        for (Element element : structMaps) {
            if (element.getAttributeValue("TYPE").contentEquals("PHYSICAL")) {
                physStruct = element;
            } else if (element.getAttributeValue("TYPE").contentEquals("LOGICAL")) {
                logStruct = element;
            }
        }

        List<Element> origLogStructs = ((Element) logStruct.getChildren().get(0)).getChildren();
        if (origLogStructs == null || origLogStructs.isEmpty()) {
            origLogStructs = new ArrayList<Element>();
            origLogStructs.add((Element) logStruct.getChildren().get(0));
        }
        logStruct.removeContent();
        List<Element> pages = getPhysicalPages(physStruct, true);
        List documentStruct = physStruct.removeContent();
        if (dsAnchorType == null) {
            int count = 0;
            while (!(documentStruct.get(count) instanceof Element)) {
                count++;
            }
            documentStruct = ((Element) documentStruct.get(count)).removeContent();
        }
        //        physStruct.removeContent();

        //create new Physical DocStruct
        Element boundBook = new Element("div", mets);
        boundBook.setAttribute("ID", "PHYS_0000");
//        boundBook.setAttribute("DMDID", "DMDPHYS_0000");
        boundBook.setAttribute("TYPE", "BoundBook");
        int pageCount = 1;
        for (Element page : pages) {
            page.setAttribute("TYPE", "page");
            String labelString = page.getAttributeValue("LABEL");
            String orderlabelString = page.getAttributeValue("ORDERLABEL");
            page.setAttribute("LABEL", orderlabelString);
            page.setAttribute("ORDERLABEL", labelString);
            page.setAttribute("ORDER", "" + pageCount);
            boundBook.addContent(page.detach());
            pageCount++;
        }
        physStruct.addContent(boundBook);

        //create new Logical DocStruct
        logStruct.setContent(documentStruct);
        Element eleDocument = (Element) logStruct.getChildren().get(0);
        if(dsAnchorType != null) {
            eleDocument.setAttribute("TYPE", "ArchiveDocument");
            eleDocument = (Element) eleDocument.getChildren().get(0);
        }
        eleDocument.setAttribute("TYPE", "CompoundDocument");
        eleDocument.setAttribute("DMDID", origLogStructs.get(0).getAttributeValue("DMDID"));
        eleDocument.setAttribute("ADMID", origLogStructs.get(0).getAttributeValue("ADMID"));

        Iterator<Element> itemIterator = origLogStructs.iterator();

        for (Object obj : ((Element) logStruct.getChildren().get(0)).getChildren()) {
            if (obj instanceof Element) {
                correctArchiveDocStruct((Element) obj, itemIterator);
            }
        }

        return doc;

    }

    private void correctArchiveDocStruct(Element ele, Iterator<Element> itemIterator) {
        List<Element> children = ele.getChildren();
        if (children != null && !children.isEmpty()) {
            //This is a compount item
            ele.setAttribute("TYPE", "CompoundDocument");
            for (Element child : children) {
                correctArchiveDocStruct(child, itemIterator);
            }
        } else {
            //This is a simple item: retrieve ids from the corresponding logical item
            ele.setAttribute("TYPE", "SimpleDocument");
            if (itemIterator.hasNext()) {
                Element origEle = itemIterator.next();
                itemTitleList.add(origEle.getAttributeValue("LABEL"));
                ele.setAttribute("ID", origEle.getAttributeValue("ID"));
            } else {
                logger.error("Found a simple document in phys struct, but no corresponding element in log struct");
            }
        }

    }

    /**
     * 
     * makes the physical and logical structMap of doc compatible with goobi
     * 
     * @param doc
     * @param anchorElement the document's anchor as jDom Element. must be inserted into the ff afterwards
     * @return
     */
    @SuppressWarnings("unchecked")
    private Document replaceStructData(Document doc) {

        Element physStruct = null;
        Element logStruct = null;
        List<Element> structMaps = doc.getRootElement().getChildren("structMap", mets);

        // set filegroup use to local
        Element fileSec = doc.getRootElement().getChild("fileSec", mets);
        if (fileSec != null) {
            Element fileGrp = fileSec.getChild("fileGrp", mets);
            fileGrp.setAttribute("USE", "LOCAL");
        }

        for (Element element : structMaps) {
            if (element.getAttributeValue("TYPE").contentEquals("PHYSICAL")) {
                physStruct = element;
            } else if (element.getAttributeValue("TYPE").contentEquals("LOGICAL")) {
                logStruct = element;
            }
        }

        // if we don't know the logical struct types, set them to Document/Item
        if (logStruct != null) {
            List<Element> logChildren = logStruct.getChildren("div", mets);
            if (logChildren != null) {
                for (Element element : logChildren) {
                    element.setAttribute("TYPE", "DOCUMENT");
                    List<Element> logRootChildren = element.getChildren("div", mets);
                    if (logRootChildren != null && !logRootChildren.isEmpty()) {
                        for (Element child : logRootChildren) {
                            child.setAttribute("TYPE", "ITEM");

                        }
                    }
                }
            }

        }

        // make physDocStrct comply to (Collection->)BoundBook->page
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
        physRoot.setAttribute("TYPE", "Collection");
        List<Element> books = new ArrayList<Element>();
        books.add(physRoot);
        List<Element> pages = getPhysicalPages(books.get(0), false);
        while (pages.size() == 0) {
            books = books.get(0).getChildren();
            for (Element book : books) {
                book.setAttribute("TYPE", "Collection");
                pages.addAll(getPhysicalPages(book, false));
            }
        }
        for (Element book : books) {
            // book.setAttribute("TYPE", "Collection");
            book.setAttribute("TYPE", "BoundBook");
        }
        for (Element page : pages) {
            page.setAttribute("TYPE", "page");
            String labelString = page.getAttributeValue("LABEL");
            String orderlabelString = page.getAttributeValue("ORDERLABEL");
            page.setAttribute("LABEL", orderlabelString);
            page.setAttribute("ORDERLABEL", labelString);
        }

        return doc;
    }

    private ArrayList<Element> getPhysicalPages(Element parent, boolean recursive) {

        ArrayList<Element> pages = new ArrayList<Element>();

        List children = parent.getChildren("div", mets);
        if (children == null || children.isEmpty()) {
            return pages;
        }
        int volume = -1;
        try {
            volume = Integer.valueOf(parent.getAttributeValue("ORDER"));
        } catch (Exception e) {

        }
        for (Object object : children) {
            if (object instanceof Element) {
                Element child = (Element) object;
                if (child.getChild("fptr", mets) != null) { // a page

                    // child.getAttributeValue("TYPE").toLowerCase().contentEquals("page") ||
                    // child.getAttributeValue("TYPE").toLowerCase().contentEquals("duplex") ) {
                    // child is a page
                    pages.add(child);
                    if (volume != -1) {
                        // map the volume this page belongs to
                        pageVolumeMap.put(child.getAttributeValue("ID"), volume);
                    }

                } else {
                    if (recursive) {
                        pages.addAll(getPhysicalPages(child, true));
                    }
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
    private Document swapStructData(Document doc) {

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

        // get old and new Dmd sections
        List<Element> newDmdSecs = marcDoc.getRootElement().getChildren("dmdSec", mets);

        String dmdID1 = ((Element) newDmdSecs.get(0)).getAttributeValue("ID");
        String dmdIDpyhs = null;
        String dmdID2 = null;
        if (newDmdSecs.size() > 1) {
            dmdIDpyhs = ((Element) newDmdSecs.get(newDmdSecs.size()-1)).getAttributeValue("ID");
        }
        if(newDmdSecs.size() > 2) {            
            dmdID2 = ((Element) newDmdSecs.get(1)).getAttributeValue("ID");
        }
        
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
                dmdID1 = element.getAttributeValue("ID");
                Element dmdChild = (Element) newDmdSecs.get(0).getChild("mdWrap", mets).clone();
                element.setContent(dmdChild);
                doc.getRootElement().addContent(element);

                if (newDmdSecs.size() > 1) // check if we have indeed two dmdSecs
                {
                    for (int i = 1; i <newDmdSecs.size(); i++) {                        
                        Element newDmdSec2 = (Element) newDmdSecs.get(i).clone();
//                        dmdIDpyhs = newDmdSec2.getAttributeValue("ID");
                        doc.getRootElement().addContent(newDmdSec2);
                    }
                }
            } else {
                // all other elements, just reattach
                doc.getRootElement().addContent(element);
                // set dmdid for boundbook
                if (dmdIDpyhs != null && element.getName().contentEquals("structMap") && element.getAttributeValue("TYPE").contentEquals("PHYSICAL")) {
                    logger.debug("adding reference DMDID=" + dmdIDpyhs + " to physical structMap");
                    Element book = element.getChild("div", mets);
                    book.setAttribute("DMDID", dmdIDpyhs);
                }
                //set dmdid for second logical struct
                if (element.getName().contentEquals("structMap") && element.getAttributeValue("TYPE").contentEquals("LOGICAL")) {
                    logger.debug("adding reference DMDID=" + dmdID1 + " to top logical struct");
                    Element logical1 = element.getChild("div", mets);
                    Element logical2 = logical1.getChild("div", mets);
                    
                    if(dmdID2 != null) {
                        logger.debug("adding reference DMDID=" + dmdID2 + " to second logical struct");
                        logical1.setAttribute("DMDID", dmdID1);
                        logical2.setAttribute("DMDID", dmdID2);
                    } else {
                        logical2.setAttribute("DMDID", dmdID1);
                    }
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

        List<Record> recordList = new ArrayList<Record>();
        HashMap<Record, File> updateRecordMap = new HashMap<Record, File>();
        for (String filename : filenames) {
            String[] parts = filename.split("::");
            if (parts == null || parts.length != 2) {
                // return recordList;
                continue;
            }
            String projectName = parts[0].trim();
            String fileName = parts[1].trim();
            File projectDir = new File(exportFolder, projectName);
            if (projectDir.isDirectory()) {
                File sourceFile = new File(projectDir, fileName);
                File tempFile = new File(TEMP_DIRECTORY, sourceFile.getName());
                try {
                    CommonUtils.copyFile(sourceFile, tempFile);
                } catch (IOException e) {
                    logger.error("Unable to copy original metadata file. Cannot import process");
                    continue;
                }
                importFile = tempFile;
                List<Record> tempList = retrieveOriginalRecordsFromFile();
                if (tempList != null) {
                    recordList.addAll(tempList);
                }
            }
        }

        recordList = generateRecordsForImport(recordList);

        return recordList;
    }

    @Override
    public List<ImportProperty> getProperties() {
        return null;
    }

    @Override
    public List<String> getAllFilenames() {
        ArrayList<String> projectList = new ArrayList<String>(projectsCollectionsMap.keySet());
        ArrayList<String> filenameList = new ArrayList<String>();
        String metsDirName = "";
        try {
            for (String project : projectList) {
                File projectDir = new File(exportFolder, project);
                if (projectDir.isDirectory()) {
                    File[] subDirs = projectDir.listFiles(MetsDirFilter);
                    File[] fileList = null;
                    if (subDirs != null) {
                        for (File metsDir : subDirs) {
                            fileList = metsDir.listFiles(MetsFilter);
                            if (fileList != null && fileList.length > 0) {
                                metsDirName = metsDir.getName() + File.separator;
                                break;
                            }
                        }
                    }
                    if (fileList == null || fileList.length == 0) {
                        fileList = projectDir.listFiles(MetsFilter);
                    }
                    if (fileList != null && fileList.length > 0) {
                        for (File file : fileList) {
                            // if(updateExistingRecords) {
                            filenameList.add(project + "::\t" + metsDirName + file.getName());
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

    private boolean splitPdf(File pdfFile, File destDir, PdfExtractor extractor) {

        if (pdfFile == null || !pdfFile.isFile()) {
            return false;
        }

        if (destDir == null || !destDir.exists()) {
            destDir.mkdirs();
        }

        if (extractor == null) {
            extractor = new PdfExtractor();
        }

        return extractor.extractPdfs(pdfFile, destDir, null);

    }

    @Override
    public void deleteFiles(List<String> selectedFilenames) {
        if (importFile != null && importFile.isFile()) {
            importFile.delete();
        }

    }

    private void copyAllMetadata(DocStruct source, DocStruct target) {
        if (source.getAllMetadata() != null) {
            for (Metadata md : source.getAllMetadata()) {
                try {
                    target.addMetadata(md);
                } catch (MetadataTypeNotAllowedException e) {
                    logger.error(e.toString());
                } catch (DocStructHasNoTypeException e) {
                    logger.error(e.toString());
                }
            }
        }
        if (source.getAllPersons() != null) {
            for (Person md : source.getAllPersons()) {
                try {
                    target.addPerson(md);
                } catch (MetadataTypeNotAllowedException e) {
                    logger.error(e.toString());
                } catch (DocStructHasNoTypeException e) {
                    logger.error(e.toString());
                }
            }
        }
    }

    @Override
    public List<DocstructElement> getCurrentDocStructs() {
        return null;
    }

    @Override
    public String deleteDocstruct() {
        return null;
    }

    @Override
    public String addDocstruct() {
        return null;
    }

    @Override
    public List<String> getPossibleDocstructs() {
        return null;
    }

    @Override
    public DocstructElement getDocstruct() {
        return null;
    }

    @Override
    public void setDocstruct(DocstructElement dse) {
    }

    public Prefs getPrefs() {
        return prefs;
    }

    public String getCurrentSuffix() {
        return identifierSuffix;
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

    /**
     * Sort Volume DocStructs to correspond to theit volume numbers or identifiers
     * 
     * @author florian
     * 
     */
    public class VolumeComparator implements Comparator<DocStruct> {

        @Override
        public int compare(DocStruct d1, DocStruct d2) {
            if (d1 == null || d2 == null || d1.getIdentifier() == null || d2.getIdentifier() == null) {
                return 0;
            }

            String id1 = d1.getIdentifier().replaceAll("\\D", "");
            String id2 = d2.getIdentifier().replaceAll("\\D", "");
            if (id1 == null || id2 == null || id1.isEmpty() || id2.isEmpty()) {
                return 0;
            }
            int result = Integer.valueOf(id1) - Integer.valueOf(id2);

            if (result == 0) {
                // if both numbers are the same, sort by other criteria
                String[] p1 = d1.getIdentifier().split("_");
                String[] p2 = d2.getIdentifier().split("_");

                if (p1 == null || p1.length == 0 || p2 == null || p2.length == 0) {
                    return 0;
                }
                // first try to sort by number of parts
                result = ((Integer) (p1.length)).compareTo((Integer) (p2.length));

                if (result == 0) {
                    // Then sort by part comparison (last part first, since it is probably the volume id)
                    for (int i = p2.length - 1; i > -1; i--) {
                        result = p1[i].compareTo(p2[i]);
                        if (result != 0) {
                            break;
                        }
                    }
                }
            }
            return result;
        }
    }

    /**
     * Comparator to sort image folders
     * 
     * @author florian
     * 
     */
    public class ProcessFileComparator implements Comparator<File> {

        @Override
        public int compare(File f1, File f2) {
            if (f1 == null || f2 == null) {
                return 0;
            }
            String s1 = f1.getName();
            String s2 = f2.getName();

            String[] p1 = s1.split("_");
            String[] p2 = s2.split("_");

            // compare full Strings only if we cannot split them
            if (p1 == null || p2 == null || p1.length < 2 || p2.length < 2) {
                return s1.compareTo(s2);
            }

            // Compare the second strings (first strings are == "M")
            if (!p1[1].contentEquals(p2[1])) {
                return p1[1].compareTo(p2[1]);
            }

            String v1 = p1[p1.length - 1];
            String v2 = p2[p2.length - 1];
            // compare the last Strings if they are volume identifiers
            if (v1 != null && v2 != null && v1.startsWith("V") && v2.startsWith("V") && !v1.contentEquals(v2)) {
                return v1.compareTo(v2);
            }

            // try to compare all parts of the string
            for (int i = 0; i < Math.min(p1.length, p2.length); i++) {
                if (p1.length > i + 1 && p2.length > i + 1 && p1[i] != null && p2[i] != null && !p1[i].contentEquals(p2[i])) {
                    return p1[i].compareTo(p2[i]);
                }
            }

            // compare by number of string parts
            if (p1.length != p2.length) {
                return ((Integer) (p1.length)).compareTo((Integer) (p2.length));
            }

            return s1.compareTo(s2);
        }
    }

    public String getId() {
        // TODO Auto-generated method stub
        return null;
    }

}
